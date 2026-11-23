module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DeRhamVectorExtension
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearCanonicalMapPrimitiveDeRhamRigExt
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalRigidifiedExtensionOfDeRhamClassUnique
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHodgeFiltrationToPDivOmegaLinearMapStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusCanonicalLiftPrimitiveHodgeStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalRigidifiedExtensionPullbackNaturality
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamToRigidifiedExtensionBijectivePNilpotentStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRelativeDimensionAbelianTorsionTowerStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdicCompleteSpanNatCastOfIsNilpotent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCanForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieCotValEqTanVal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmegaLevelBijectiveOfPowEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveHodgeToOmegaSpanModMaximalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigOfOmegaInjectiveOfPow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveOfRangeSupSmulTopEqTop

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearCanonicalMapPrimitiveDeRhamRigExtStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_linear_canonical_map_primitiveDeRham_rigExt : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (p : ℕ) (G : PDivGroup p R) (t : G.TorsionTower A), IsAbelianScheme A → ∃ L : primDR A →ₗ[R] ((G.cocycles × G.omega) ⧸ _root_.LinearMap.range (G.cob.prod (_root_.LinearMap.codRestrict G.omegaSub ((_root_.LinearMap.piMap fun i => _root_.GlobalTheory.AugCot.d (_root_.Bialgebra.counitAlgHom _ (G.A i))).domRestrict G.funs) (fun b n => (_root_.GlobalTheory.PDiv.cotMap_d _ _).trans (_root_.congrArg _ (b.2 n)))))), ∀ c x, IsCan t c x ↔ L c = x := by
  first | exact @GlobalTheory.PtExt.exists_canMap | exact GlobalTheory.PtExt.exists_canMap | (intros; apply GlobalTheory.PtExt.exists_canMap <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalIsoHodgeFiltrationEqRangeInvariantForms

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem map_F1prim_eq_range_rigOfOmega (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (N : ℕ)
    (hN : (p : R) ^ N = 0) (A : Over (Sp R)) [GrpObj A] (hA : IsAbelianScheme A)
    (G : PDivGroup p R) (t : G.TorsionTower A) (L : primDR A →ₗ[R] ((G.cocycles × G.omega) ⧸ _root_.LinearMap.range (G.cob.prod (_root_.LinearMap.codRestrict G.omegaSub ((_root_.LinearMap.piMap fun i => _root_.GlobalTheory.AugCot.d (_root_.Bialgebra.counitAlgHom _ (G.A i))).domRestrict G.funs) (fun b n => (_root_.GlobalTheory.PDiv.cotMap_d _ _).trans (_root_.congrArg _ (b.2 n)))))))
    (hL : Function.Surjective L) (hc : ∀ c, IsCan t c (L c)) :
    (PrimitiveSubmodule A).map L = LinearMap.range G.rigOfOmega := by
  obtain ⟨ψ, hψ⟩ := GlobalTheory.T.exists_hodgeFiltration_to_pDivOmega_linearMap p R N hN A hA G t
  apply le_antisymm
  · rintro _ ⟨c, hcF, rfl⟩
    refine ⟨ψ ⟨c, hcF⟩, ?_⟩
    exact GlobalTheory.PtExt.isCan_unique R A p G t c hA _ _ (hψ ⟨c, hcF⟩) (hc c)
  · rintro _ ⟨w, rfl⟩
    obtain ⟨c, hcw⟩ := hL (G.rigOfOmega w)
    refine ⟨c, GlobalTheory.T.mem_primitiveSubmodule_of_isCan_of_rigToExt_eq_zero p R N hN A hA G t c (L c) (hc c) ?_, hcw⟩
    rw [hcw]
    exact G.exact_rigOfOmega_rigToExt.apply_apply_eq_zero w

end GlobalTheory.PtExt
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalIsoHodgeFiltrationEqRangeInvariantFormsStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.canonical_iso_hodge_filtration_eq_range_invariant_forms : ∀ (p : ℕ) [Fact p.Prime]  (R : Type) [CommRing R] (N : ℕ), (p : R) ^ N = 0 → ∀ (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ (G : PDivGroup p R) (t : G.TorsionTower A) (L : primDR A →ₗ[R] ((G.cocycles × G.omega) ⧸ _root_.LinearMap.range (G.cob.prod (_root_.LinearMap.codRestrict G.omegaSub ((_root_.LinearMap.piMap fun i => _root_.GlobalTheory.AugCot.d (_root_.Bialgebra.counitAlgHom _ (G.A i))).domRestrict G.funs) (fun b n => (_root_.GlobalTheory.PDiv.cotMap_d _ _).trans (_root_.congrArg _ (b.2 n))))))), Function.Surjective L → (∀ c, IsCan t c (L c)) → (PrimitiveSubmodule A).map L = LinearMap.range G.rigOfOmega := by
  first | exact @GlobalTheory.PtExt.map_F1prim_eq_range_rigOfOmega | exact GlobalTheory.PtExt.map_F1prim_eq_range_rigOfOmega | (intros; apply GlobalTheory.PtExt.map_F1prim_eq_range_rigOfOmega <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalRigidifiedExtensionPullbackNaturalityStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.canonicalRigidifiedExtension_pullback_naturality : ∀ (p : ℕ) (R R' : Type) [CommRing R] [CommRing R'] (A : Over (Sp R)) [GrpObj A] (A' : Over (Sp R')) [GrpObj A'] (G : PDivGroup p R) (G' : PDivGroup p R') (t : G.TorsionTower A) (t' : G'.TorsionTower A') (σ : R →+* R') (φ : A'.left ⟶ A.left) (m : GrpMor (dp0 R) (𝟙 _) A (dp0 R') (𝟙 _) A' σ (spMap σ) φ) (c : primDR A) (x : ((G.cocycles × G.omega) ⧸ _root_.LinearMap.range (G.cob.prod (_root_.LinearMap.codRestrict G.omegaSub ((_root_.LinearMap.piMap fun i => _root_.GlobalTheory.AugCot.d (_root_.Bialgebra.counitAlgHom _ (G.A i))).domRestrict G.funs) (fun b n => (_root_.GlobalTheory.PDiv.cotMap_d _ _).trans (_root_.congrArg _ (b.2 n))))))), IsCan t c x → IsCan t' (m.pull c) ((t'.semiHom t m).rig x) := by
  first | exact @GlobalTheory.PtExtNat.isCan_pull | exact GlobalTheory.PtExtNat.isCan_pull | (intros; apply GlobalTheory.PtExtNat.isCan_pull <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieImageIffLieCorrespondenceDeRhamExtension

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.PtExt



theorem isLieImage_iff_lieCorr : GlobalTheory.Published.AbelianHodgeDeRham → ∀ (p : ℕ) [Fact p.Prime]  (R : Type) [CommRing R], IsNilpotent (p : R) → ∀ (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (G : PDivGroup p R) (t : G.TorsionTower A) (E : primDR A ≃ₗ[R] ((G.cocycles × G.omega) ⧸ _root_.LinearMap.range (G.cob.prod (_root_.LinearMap.codRestrict G.omegaSub ((_root_.LinearMap.piMap fun i => _root_.GlobalTheory.AugCot.d (_root_.Bialgebra.counitAlgHom _ (G.A i))).domRestrict G.funs) (fun b n => (_root_.GlobalTheory.PDiv.cotMap_d _ _).trans (_root_.congrArg _ (b.2 n))))))), (∀ c, IsCan t c (E c)) → ∀ (h : HdR A) (v : epsR R ⟶ A), IsLieImage h v ↔ t.LieCorr (G.lieUnivToLie (E.symm.dualMap h)) v := by
  intro hHdR p _ R _ hnil A _ g hA hsm G t E hE h v
  obtain ⟨N, hN⟩ := hnil
  haveI := isAdicComplete_span_natCast_of_isNilpotent p R ⟨N, hN⟩

  have key : ∀ (β : Form (A.hom ≫ 𝟙 _)) (hβ : Form.cl _ β ∈ primDR A) (w : G.omega),
      IsCan t ⟨_, hβ⟩ (G.rigOfOmega w) → G.lieUnivToLie (E.symm.dualMap h) w = h ⟨_, hβ⟩ := by
    intro β hβ w hw
    have e : E ⟨_, hβ⟩ = G.rigOfOmega w := isCan_unique R A p G t _ hA _ _ (hE _) hw
    change (E.symm.dualMap h) (G.rigOfOmega w) = _
    change h (E.symm (G.rigOfOmega w)) = _
    rw [← e, LinearEquiv.symm_apply_apply]
  constructor
  · rintro ⟨hv, hh⟩
    obtain ⟨x', hx', -⟩ := t.existsUnique_lieCorr hv
    obtain ⟨ψ, hψ⟩ := T.exists_hodgeFiltration_to_pDivOmega_linearMap p R N hN A hA G t
    haveI : Module.Finite R G.omega := .equiv (LinearEquiv.ofBijective _
      (PDivGroup.omegaLevel_bijective_of_pow_eq_zero p R N hN G N le_rfl)).symm
    have hs := surjective_of_range_sup_smul_top_eq_top R _ _ ψ
      (T.primitive_hodge_to_omega_span_mod_maximal hHdR p R N hN A g hA hsm G t ψ hψ)
    suffices e : x' = G.lieUnivToLie (E.symm.dualMap h) by rw [← e]; exact hx'
    refine LinearMap.ext fun w => ?_
    obtain ⟨c, rfl⟩ := hs w
    obtain ⟨c, hF⟩ := c
    have hF' := hF
    change c.1 ∈ F1 _ at hF'
    rw [hodgeFiltration_eq_range] at hF'
    obtain ⟨c, hc⟩ := c
    obtain ⟨β, rfl⟩ := hF'
    obtain ⟨w, hw1, hw2⟩ := isCan_form R A p G t β hc
    have hw : ψ ⟨_, hF⟩ = w :=
      PDivGroup.rigOfOmega_injective_of_pow p R N hN G (isCan_unique R A p G t _ hA _ _ (hψ _) hw2)
    rw [key β hc _ (hψ ⟨_, hF⟩), hw, lie_cotVal_eq_tanVal R A p G t ⟨N, hN⟩ β w hw1 x' v hx', hh β hc]
  · intro hx
    refine ⟨hx.1, fun β hβ => ?_⟩
    obtain ⟨w, hw1, hw2⟩ := isCan_form R A p G t β hβ
    rw [← key β hβ w hw2]
    exact lie_cotVal_eq_tanVal R A p G t ⟨N, hN⟩ β w hw1 _ v hx

end GlobalTheory.PtExt
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieImageIffLieCorrespondenceDeRhamExtensionStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.lie_image_iff_lie_correspondence_deRham_extension : GlobalTheory.Published.AbelianHodgeDeRham → ∀ (p : ℕ) [Fact p.Prime]  (R : Type) [CommRing R], IsNilpotent (p : R) → ∀ (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (G : PDivGroup p R) (t : G.TorsionTower A) (E : primDR A ≃ₗ[R] ((G.cocycles × G.omega) ⧸ _root_.LinearMap.range (G.cob.prod (_root_.LinearMap.codRestrict G.omegaSub ((_root_.LinearMap.piMap fun i => _root_.GlobalTheory.AugCot.d (_root_.Bialgebra.counitAlgHom _ (G.A i))).domRestrict G.funs) (fun b n => (_root_.GlobalTheory.PDiv.cotMap_d _ _).trans (_root_.congrArg _ (b.2 n))))))), (∀ c, IsCan t c (E c)) → ∀ (h : HdR A) (v : epsR R ⟶ A), IsLieImage h v ↔ t.LieCorr (G.lieUnivToLie (E.symm.dualMap h)) v := by
  first | exact @GlobalTheory.PtExt.isLieImage_iff_lieCorr | exact GlobalTheory.PtExt.isLieImage_iff_lieCorr | (intros; apply GlobalTheory.PtExt.isLieImage_iff_lieCorr <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCanonicalDeRhamRigidExtensionFamily

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.DeRhamExt

def canMap (p : ℕ) {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] (hA : IsAbelianScheme A)
    {G : PDivGroup p R} (t : G.TorsionTower A) : primDR A →ₗ[R] ((G.cocycles × G.omega) ⧸ _root_.LinearMap.range (G.cob.prod (_root_.LinearMap.codRestrict G.omegaSub ((_root_.LinearMap.piMap fun i => _root_.GlobalTheory.AugCot.d (_root_.Bialgebra.counitAlgHom _ (G.A i))).domRestrict G.funs) (fun b n => (_root_.GlobalTheory.PDiv.cotMap_d _ _).trans (_root_.congrArg _ (b.2 n)))))) :=
  Classical.choose (GlobalTheory.T.exists_linear_canonical_map_primitiveDeRham_rigExt R A p G t hA)

theorem isCan_iff_canMap (p : ℕ) {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A]
    (hA : IsAbelianScheme A) {G : PDivGroup p R} (t : G.TorsionTower A) (c : primDR A)
    (x : ((G.cocycles × G.omega) ⧸ _root_.LinearMap.range (G.cob.prod (_root_.LinearMap.codRestrict G.omegaSub ((_root_.LinearMap.piMap fun i => _root_.GlobalTheory.AugCot.d (_root_.Bialgebra.counitAlgHom _ (G.A i))).domRestrict G.funs) (fun b n => (_root_.GlobalTheory.PDiv.cotMap_d _ _).trans (_root_.congrArg _ (b.2 n))))))) : IsCan t c x ↔ canMap p hA t c = x :=
  Classical.choose_spec (GlobalTheory.T.exists_linear_canonical_map_primitiveDeRham_rigExt R A p G t hA) c x

theorem isCan_canMap (p : ℕ) {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A]
    (hA : IsAbelianScheme A) {G : PDivGroup p R} (t : G.TorsionTower A) (c : primDR A) :
    IsCan t c (canMap p hA t c) :=
  (isCan_iff_canMap p hA t c _).2 rfl

theorem canMap_bijective (hP : GlobalTheory.Published.AbelianHodgeDeRham) (p : ℕ) [Fact p.Prime] {R : Type}
    [CommRing R] (hR : IsNilpotent (p : R)) {A : Over (Sp R)} [GrpObj A] (hA : IsAbelianScheme A)
    {G : PDivGroup p R} (t : G.TorsionTower A) : Function.Bijective (canMap p hA t) := by
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_relativeDimension_abelian_torsionTower hP p R hR A hA G t
  exact GlobalTheory.T.deRham_to_rigidified_extension_bijective_p_nilpotent hP p R hR A g hA hg G t _ (isCan_canMap p hA t)

def canFamily (hP : GlobalTheory.Published.AbelianHodgeDeRham) (p : ℕ) [Fact p.Prime] :
    GlobalTheory.Published.DeRhamVectorExtension.Family p :=
  fun _ _ hR _ _ hA _ t => LinearEquiv.ofBijective (canMap p hA t) (canMap_bijective hP p hR hA t)

theorem exists_canonical_family : GlobalTheory.Published.AbelianHodgeDeRham → ∀ (p : ℕ) [Fact p.Prime],
    ∃ e : GlobalTheory.Published.DeRhamVectorExtension.Family p, e.Natural ∧ e.Filtered ∧ e.Tangent ∧
      ∀ ⦃R : Type⦄ [CommRing R] (hR : IsNilpotent (p : R)) ⦃A : Over (Sp R)⦄ [GrpObj A]
        (hA : IsAbelianScheme A) ⦃G : PDivGroup p R⦄ (t : G.TorsionTower A) (c : primDR A),
        IsCan t c (e hR hA t c) := by
  intro hP p _
  refine ⟨canFamily hP p, ?_, ?_, ?_, ?_⟩
  · intro R R' _ _ hR hR' A _ A' _ hA hA' G G' t t' σ φ m c
    exact ((isCan_iff_canMap p hA' t' _ _).1
      (GlobalTheory.T.canonicalRigidifiedExtension_pullback_naturality p R R' A A' G G' t t' σ φ m c _ (isCan_canMap p hA t c)))
  · intro R _ hR A _ hA G t
    obtain ⟨N, hN⟩ := hR
    exact GlobalTheory.T.canonical_iso_hodge_filtration_eq_range_invariant_forms p R N hN A hA G t (canMap p hA t)
      (canMap_bijective hP p ⟨N, hN⟩ hA t).2 (isCan_canMap p hA t)
  · intro R _ hR A _ hA G t h v
    obtain ⟨g, hg⟩ := GlobalTheory.T.exists_relativeDimension_abelian_torsionTower hP p R hR A hA G t
    exact GlobalTheory.T.lie_image_iff_lie_correspondence_deRham_extension hP p R hR A g hA hg G t (canFamily hP p hR hA t)
      (isCan_canMap p hA t) h v
  · intro R _ hR A _ hA G t c
    exact isCan_canMap p hA t c

end GlobalTheory.DeRhamExt
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCanonicalDeRhamRigidExtensionFamilyStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_canonical_deRham_rigidExtension_family : GlobalTheory.Published.AbelianHodgeDeRham → ∀ (p : ℕ) [Fact p.Prime], ∃ e : GlobalTheory.Published.DeRhamVectorExtension.Family p, e.Natural ∧ e.Filtered ∧ e.Tangent ∧ ∀ ⦃R : Type⦄ [CommRing R] (hR : IsNilpotent (p : R)) ⦃A : Over (Sp R)⦄ [GrpObj A] (hA : IsAbelianScheme A) ⦃G : PDivGroup p R⦄ (t : G.TorsionTower A) (c : primDR A), IsCan t c (e hR hA t c) := by
  first | exact @GlobalTheory.DeRhamExt.exists_canonical_family | exact GlobalTheory.DeRhamExt.exists_canonical_family | (intros; apply GlobalTheory.DeRhamExt.exists_canonical_family <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamVectorExtensionIsoOfHodgeDeRham

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem deRhamVectorExtension_of_abelianHodgeDeRham :
    GlobalTheory.Published.AbelianHodgeDeRham → GlobalTheory.Published.DeRhamVectorExtension := by
  intro hHdR p _
  obtain ⟨e, hN, hF, hT, -⟩ := GlobalTheory.T.exists_canonical_deRham_rigidExtension_family hHdR p
  exact ⟨e, hN, hF, hT⟩

end GlobalTheory
end
end
