module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernClassContractionTangentEqTorsorCocycleStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDeRhamFreeHodgeSequenceBaseChangeStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocycleCohomologousOfDeRhamSurjective
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamToH1StructureSurjectiveAbelian
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.KerIdealCompOfSurjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointwiseCocycleOnCoverExtendsUpToCoboundaryStatement
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PreimageEqTopOfSurjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentPullbackPrimitiveCrystallineClassEpsPartI
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChernRepresentativeContractionOfOrthogonalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTangentVectorContractionTwoCochainProduct

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocycleCohomologousOfDeRhamSurjectiveStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.cocycle_cohomologous_of_de_rham_surjective : ∀ (R : Type) [CommRing R] (X : Over (Sp R)), Function.Surjective (toH1O (X.hom ≫ 𝟙 _)) → ∀ u : Fn1 X, IsCoc (whole X) u → ∃ f : Z1 (O (dp0 R) (X.hom ≫ 𝟙 _)), Cohom (whole X) u (fv f) := by
  first | exact @GlobalTheory.PtExt.cohom_fv_of_toH1O_surjective | exact GlobalTheory.PtExt.cohom_fv_of_toH1O_surjective | (intros; apply GlobalTheory.PtExt.cohom_fv_of_toH1O_surjective <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamToH1StructureSurjectiveAbelianStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.de_rham_to_h1_structure_surjective_abelian : GlobalTheory.Published.AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → Function.Surjective (toH1O (A.hom ≫ 𝟙 _)) := by
  first | exact @GlobalTheory.PtExt.toH1O_surjective_of_abelian | exact GlobalTheory.PtExt.toH1O_surjective_of_abelian | (intros; apply GlobalTheory.PtExt.toH1O_surjective_of_abelian <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SndPullCohomZero

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

variable {R : Type} [CommRing R]

theorem spOver_epsHom_ptV {A B : Over (Sp R)} [GrpObj A] [GrpObj B] (v : epsR R ⟶ B)
    {D D' : Type} [CommRing D] [Algebra R D] [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D') (x : Pt A D) :
    (spOver (epsHom φ) ≫ ptV v x : Pt (A ⊗ B) (DualNumber D')) =
      ptV v (spOver φ ≫ x : Pt A D') := by
  have h1 : (epsHom φ).comp (TrivSqZeroExt.inlAlgHom R D D) = (TrivSqZeroExt.inlAlgHom R D' D').comp φ :=
    AlgHom.ext fun a ↦ by simp [epsHom]
  have h2 : (epsHom φ).comp (EpsWeil.epsMap R D) = EpsWeil.epsMap R D' :=
    DualNumber.algHom_ext (by simp [epsHom, EpsWeil.epsMap, DualNumber.lift_apply_apply])
  simp only [ptV, comp_lift, ← Category.assoc, spOver_comp, h1, h2]

theorem fst_ptV {A B : Over (Sp R)} [GrpObj A] [GrpObj B] {v : epsR R ⟶ B} (hv : IsTangent v)
    {D : Type} [CommRing D] [Algebra R D] (x : Pt A D) :
    (spOver (TrivSqZeroExt.fstHom R D D) ≫ ptV v x : Pt (A ⊗ B) D) = pt0 B x := by
  have h1 : (TrivSqZeroExt.fstHom R D D).comp (TrivSqZeroExt.inlAlgHom R D D) = AlgHom.id R D :=
    AlgHom.ext fun _ ↦ rfl
  have h2 : (TrivSqZeroExt.fstHom R D D).comp (EpsWeil.epsMap R D) =
      (Algebra.ofId R D).comp (TrivSqZeroExt.fstHom R R R) :=
    DualNumber.algHom_ext (by simp [EpsWeil.epsMap, DualNumber.lift_apply_apply])
  rw [ptV, pt0, comp_lift, ← Category.assoc, spOver_comp, h1, spOver_id, Category.id_comp,
    ← Category.assoc, spOver_comp, h2, ← spOver_comp, Category.assoc]
  congr 1
  ext1
  rw [Over.comp_left, Over.comp_left, spOver_left, spOver_left, Hom.one_def, Over.comp_left, Over.toUnit_left]
  have := hv
  unfold IsTangent at this
  erw [this]
  rfl

theorem sm_ptV {A B : Over (Sp R)} [GrpObj A] [GrpObj B] (P : LB (A ⊗ B).left) {v : epsR R ⟶ B}
    (hv : IsTangent v) {D : Type} [CommRing D] [Algebra R D] {x : Pt A D}
    (hx : Sm (chartsA (A := A) (B := B) P) x) : Sm (X := A ⊗ B) P.U (ptV v x) := by
  obtain ⟨i, hi⟩ := hx
  refine ⟨i, ?_⟩
  have hsurj : Surjective (spOver (TrivSqZeroExt.fstHom R D D)).left := by
    rw [spOver_left]
    refine GlobalTheory.TorusLift.surjective_specMap _ (fun a ↦ ⟨TrivSqZeroExt.inl a, rfl⟩) ⟨2, ?_⟩
    rw [sq, Ideal.zero_eq_bot, eq_bot_iff]
    refine Ideal.mul_le.2 fun a ha b hb ↦ ?_
    have ha' : a.fst = 0 := ha
    have hb' : b.fst = 0 := hb
    rw [Ideal.mem_bot]
    ext <;> simp [ha', hb']
  have e : (spOver (TrivSqZeroExt.fstHom R D D) ≫ ptV v x : Pt (A ⊗ B) D).left =
      x.left ≫ (AbDual.inl A B).left := by
    rw [fst_ptV hv, ← Over.comp_left, pt0, AbDual.inl, comp_lift, Category.comp_id, MonObj.comp_one]
  have := GlobalTheory.TorusLift.preimage_eq_top_of_surjective (spOver (TrivSqZeroExt.fstHom R D D)).left
    (ptV v x).left (U := P.U i) (by
      rw [← Over.comp_left, e, Scheme.Hom.comp_preimage]
      exact top_unique hi)
  exact this.ge

end GlobalTheory.PtExt
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentPullbackPrimitiveCrystallineClassEpsPartIStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.tangentPullback_primitiveCrystallineClass_epsPart_isCob : ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (f : Z1 (O (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _))), CatCoh.H1.mk _ f ∈ primDR (A ⊗ B) → ∀ v : epsR R ⟶ B, Cohom (whole A) (sndPull (fv f) v) (Fn1.zero A) := by
  first | exact @GlobalTheory.PtExt.cohom_sndPull_zero | exact GlobalTheory.PtExt.cohom_sndPull_zero | (intros; apply GlobalTheory.PtExt.cohom_sndPull_zero <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EpsPartCocycleCoboundaryOfHodgeDeRham

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PtExt

theorem sndPull_cohom_zero_of_hodgeDeRham : GlobalTheory.Published.AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (g : ℕ), IsAbelianScheme A → IsAbelianScheme B → SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g B.hom → ∀ P : LB (A ⊗ B).left, P.IsLB → ∀ v : epsR R ⟶ B, IsTangent v → ∀ u : Fn1 (A ⊗ B), IsCoc P.U u → Cohom (chartsA P) (sndPull u v) (Fn1.zero A) := by
  intro hHDR R _ A B _ _ g hA hB hgA hgB P hP v hv u hu
  have hFree : GlobalTheory.Published.AbelianDeRham.Free := (GlobalTheory.T.abelianSchemeDeRham_free_hodgeSequence_baseChange hHDR).1
  have hAB := ReciprocityTheory.ChartRestriction.G.Geo.Tor.AbelianSchemeGerms.isAbelianScheme_tensor A B hA hB
  have hgAB : SmoothOfRelativeDimension (g + g) (A ⊗ B).hom := AbDual.smooth_prod hgA hgB
  obtain ⟨u', hu', hExt⟩ :=
    GlobalTheory.T.pointwise_cocycle_on_cover_extends_up_to_coboundary R (A ⊗ B) P.ι P.U hP.cover u hu
  have hSurj := GlobalTheory.T.de_rham_to_h1_structure_surjective_abelian hHDR R (A ⊗ B) (g + g) hAB hgAB
  obtain ⟨f, hLift⟩ := GlobalTheory.T.cocycle_cohomologous_of_de_rham_surjective R (A ⊗ B) hSurj u' hu'
  have hprim : CatCoh.H1.mk _ f ∈ primDR (A ⊗ B) := by
    have h : AllPrim (dp0 R) (𝟙 _) (A ⊗ B) := (hFree R (A ⊗ B) (g + g) hAB hgAB).1
    rw [primDR, h]; trivial
  have hTan := GlobalTheory.T.tangentPullback_primitiveCrystallineClass_epsPart_isCob R A B f hprim v
  unfold Cohom at hExt hLift hTan ⊢
  obtain ⟨k1, c1⟩ := hExt
  obtain ⟨k2, c2⟩ := hLift
  obtain ⟨k3, c3⟩ := hTan
  refine ⟨fun D _ _ x ↦ (k1 (DualNumber D) (ptV v x)).snd + (k2 (DualNumber D) (ptV v x)).snd + k3 D x, ?_⟩
  intro D _ _ D' _ _ φ x hx
  have e1 := congrArg TrivSqZeroExt.snd (c1 _ _ (epsHom φ) (ptV v x) (sm_ptV P hv hx))
  have e2 := congrArg TrivSqZeroExt.snd (c2 _ _ (epsHom φ) (ptV v x) (sm_whole _))
  have e3 := c3 D D' φ x (sm_whole _)
  simp only [Fn1.add, Fn1.neg, Fn1.zero, sndPull, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_neg,
    TrivSqZeroExt.snd_sub, spOver_epsHom_ptV, snd_epsHom] at e1 e2 e3 ⊢
  rw [map_add (f := _), map_add (f := _)]
  linear_combination e1 + e2 + e3

end GlobalTheory.PtExt
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EpsPartCocycleCoboundaryOfHodgeDeRhamStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.eps_part_cocycle_coboundary_of_hodgeDeRham : GlobalTheory.Published.AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (g : ℕ), IsAbelianScheme A → IsAbelianScheme B → SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g B.hom → ∀ P : LB (A ⊗ B).left, P.IsLB → ∀ v : epsR R ⟶ B, IsTangent v → ∀ u : Fn1 (A ⊗ B), IsCoc P.U u → Cohom (chartsA P) (sndPull u v) (Fn1.zero A) := by
  first | exact @GlobalTheory.PtExt.sndPull_cohom_zero_of_hodgeDeRham | exact GlobalTheory.PtExt.sndPull_cohom_zero_of_hodgeDeRham | (intros; apply GlobalTheory.PtExt.sndPull_cohom_zero_of_hodgeDeRham <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologousNegTorsorCocycleOfOrthogonal

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.PtExt.cohom_fv_neg_tanCoc_of_orthogonal : GlobalTheory.Published.AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (g : ℕ), IsAbelianScheme A → IsAbelianScheme B → SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g B.hom → ∀ P : LB (A ⊗ B).left, P.IsLB → ∀ φ : HdR A →ₗ[R] HdR B →ₗ[R] R, AbDual.IsCorrForm (dp0 R) (𝟙 _) A B P φ → (∀ x ∈ Fil A, ∀ y ∈ Fil B, φ x y = 0) → ∀ (h' : HdR B) (v : epsR R ⟶ B), IsLieImage h' v → ∀ c : primDR A, (∀ h ∈ Fil A, φ h h' = h c) → ∀ f : Z1 (O (dp0 R) (A.hom ≫ 𝟙 _)), CatCoh.H1.mk _ f = c.1 → ∀ (j : ∀ (D : Type) [CommRing D] [Algebra R D], Pt A D → P.ι), IsChoice P j → Cohom (chartsA P) (fv f) (tanCoc P j v).neg := by
  intro H2' R _ A B _ _ g hA hB sA sB P hL φ hφ hO h' v hv c hc f hf j hj
  have hT : IsTangent v := hv.1
  obtain ⟨w, hw, hw0, hκ⟩ := GlobalTheory.T.exists_chernRepresentative_contraction_of_orthogonal H2' R A B g hA hB sA sB P hL φ hφ hO h' v hv c hc f hf
  obtain ⟨κ, hκc⟩ : ∃ κ : Fn1 A, IsContr w.1 v κ :=
    (GlobalTheory.PtExt.ContrMor.exists_contr R A B v hT).2 w.1
  obtain ⟨k1, h1⟩ := hκ κ hκc
  obtain ⟨u, hu, k2, h2⟩ := GlobalTheory.T.chernClass_contraction_tangent_eq_torsorCocycle R A B P hL v hT j hj w hw hw0 κ hκc
  obtain ⟨k3, h3⟩ := GlobalTheory.T.eps_part_cocycle_coboundary_of_hodgeDeRham H2' R A B g hA hB sA sB P hL v hT u hu
  refine ⟨fun D _ _ x ↦ k1 D x - k2 D x - k3 D x, fun D _ _ D' _ _ ψ x hx ↦ ?_⟩
  have e1 := h1 D D' ψ x (sm_whole x)
  have e2 := h2 D D' ψ x hx
  have e3 := h3 D D' ψ x hx
  simp only [Fn1.add, Fn1.neg, Fn1.zero, map_sub] at e1 e2 e3 ⊢
  linear_combination e1 - e2 - e3
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologousNegTorsorCocycleOfOrthogonalStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.cohomologous_neg_torsor_cocycle_of_orthogonal : GlobalTheory.Published.AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (g : ℕ), IsAbelianScheme A → IsAbelianScheme B → SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g B.hom → ∀ P : LB (A ⊗ B).left, P.IsLB → ∀ φ : HdR A →ₗ[R] HdR B →ₗ[R] R, AbDual.IsCorrForm (dp0 R) (𝟙 _) A B P φ → (∀ x ∈ Fil A, ∀ y ∈ Fil B, φ x y = 0) → ∀ (h' : HdR B) (v : epsR R ⟶ B), IsLieImage h' v → ∀ c : primDR A, (∀ h ∈ Fil A, φ h h' = h c) → ∀ f : Z1 (O (dp0 R) (A.hom ≫ 𝟙 _)), CatCoh.H1.mk _ f = c.1 → ∀ (j : ∀ (D : Type) [CommRing D] [Algebra R D], Pt A D → P.ι), IsChoice P j → Cohom (chartsA P) (fv f) (tanCoc P j v).neg := by
  first | exact @GlobalTheory.PtExt.cohom_fv_neg_tanCoc_of_orthogonal | exact GlobalTheory.PtExt.cohom_fv_neg_tanCoc_of_orthogonal | (intros; apply GlobalTheory.PtExt.cohom_fv_neg_tanCoc_of_orthogonal <;> assumption)
end
end
