module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RangeSubsetAbLocusOfIsProper
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCubicalStructureSemiAbelianExtensionStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericPointOfLiesOverGenericStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralImageOfField
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
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAbelianSchemeAway
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsModificationClosureOfGraph

section

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_modif_graph : ∀ (R : Type) [CommRing R] [IsDomain R] (o : Type) [CommRing o] (b : o →+* R) (Z : Scheme.{0}) (s : Z ⟶ Sp o), IsProper s → ∀ y : Sp (FractionRing R) ⟶ Z, y ≫ s = jK R ≫ spMap b → ∃ (M : Modif R) (h : M.S ⟶ Z), M.gp ≫ h = y ∧ h ≫ s = M.π ≫ spMap b := by
  intro R _ _ o _ b Z s hs y hy
  let ℓ : Sp (FractionRing R) ⟶ pullback s (spMap b) := pullback.lift y (jK R) hy
  have : QuasiCompact ℓ := inferInstance
  have : IsProper (pullback.snd s (spMap b)) := inferInstance
  refine ⟨{ S := ℓ.image
            π := ℓ.imageι ≫ pullback.snd s (spMap b)
            proper := inferInstance
            integral := isIntegral_image_of_field ℓ
            gp := ℓ.toImage
            gp_π := by rw [ℓ.toImage_imageι_assoc, pullback.lift_snd]
            dominant := inferInstance }, ℓ.imageι ≫ pullback.fst s (spMap b), ?_, ?_⟩
  · show ℓ.toImage ≫ ℓ.imageι ≫ pullback.fst s (spMap b) = y
    rw [ℓ.toImage_imageι_assoc, pullback.lift_fst]
  · show (ℓ.imageι ≫ pullback.fst s (spMap b)) ≫ s = (ℓ.imageι ≫ pullback.snd s (spMap b)) ≫ spMap b
    rw [Category.assoc, Category.assoc, pullback.condition]

end GlobalTheory.Mum
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsModificationClosureOfGraphStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_modification_closure_of_graph : ∀ (R : Type) [CommRing R] [IsDomain R] (o : Type) [CommRing o] (b : o →+* R) (Z : Scheme.{0}) (s : Z ⟶ Sp o), IsProper s → ∀ y : Sp (FractionRing R) ⟶ Z, y ≫ s = jK R ≫ spMap b → ∃ (M : Modif R) (h : M.S ⟶ Z), M.gp ≫ h = y ∧ h ≫ s = M.π ≫ spMap b := by
  first | exact @GlobalTheory.Mum.exists_modif_graph | exact GlobalTheory.Mum.exists_modif_graph | (intros; apply GlobalTheory.Mum.exists_modif_graph <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibrePulledSemiAbelianEqAbelianVariety

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open Classical

namespace GlobalTheory.MumGen

theorem genFibre_pullback : ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [GlobalTheory.ZH.ArithBase o Ω] (S : GlobalTheory.ZH.ThetaSys o Ω) (ρS : S.Real) (M : GlobalTheory.ZH.RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), S.Over₀ M U₀ → ∀ (Z : GlobalTheory.ZH.ZHOut ρS M U₀ EE) (e : Ω →+* FractionRing R₁) (M' : Modif R₁) (h : M'.S ⟶ M.Z), M'.gp ≫ h = spMap e ≫ M.pt → ∀ (A₁ : PolAV (Sp (FractionRing R₁))) (φ : A₁.A.left ⟶ ρS.P.A.left), IsGrpPullback A₁.A ρS.P.A (spMap (e.comp S.R.val.toRingHom)) φ → LBIso A₁.L (ρS.P.L.pull φ) → ∃ α : A₁.A.left ⟶ ((Over.pullback h).obj Z.G).left, IsGrpPullback A₁.A ((Over.pullback h).obj Z.G) M'.gp α ∧ LBIso A₁.L ((Z.L.L.pull (pullback.fst Z.G.hom h)).pull α) := by
  intro R₁ _ _ o Ω _ _ _ _ S ρS M U₀ EE hO Z e M' h hh A₁ φ hcart hlb
  have hr : Set.range M.pt ⊆ (U₀ : Set M.Z) := (GlobalTheory.ZH.top_le_preimage_iff _ _).1 (M.top_le_preimage_pt hO.ne)
  let x : Sp Ω ⟶ U₀.toScheme := IsOpenImmersion.lift U₀.ι M.pt (by rw [Scheme.Opens.range_ι]; exact hr)
  have hx : x ≫ U₀.ι = M.pt := IsOpenImmersion.lift_fac _ _ _
  have hy₀ : (spMap e ≫ x) ≫ Z.u₀ = spMap (e.comp S.R.val.toRingHom) := by
    rw [Category.assoc, Z.u₀_gen x hx, ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap_comp]
  have w₁ : φ ≫ ρS.P.A.hom = (A₁.A.hom ≫ (spMap e ≫ x)) ≫ Z.u₀ := by
    rw [hcart.1.w, Category.assoc, hy₀]
  let lam : A₁.A.left ⟶ pullback ρS.P.A.hom Z.u₀ := pullback.lift φ (A₁.A.hom ≫ (spMap e ≫ x)) w₁
  have hlam : IsGrpPullback A₁.A ((Over.pullback Z.u₀).obj ρS.P.A) (spMap e ≫ x) lam :=
    IsGrpPullback.cancel (isGrpPullback_pullback ρS.P.A Z.u₀)
      (hcart.congr hy₀.symm (pullback.lift_fst _ _ _).symm) (pullback.lift_snd _ _ _)
  have hcomp : IsGrpPullback A₁.A Z.G ((spMap e ≫ x) ≫ U₀.ι) (lam ≫ Z.φ) := IsGrpPullback.comp hlam Z.cart
  have hyy : (spMap e ≫ x) ≫ U₀.ι = M'.gp ≫ h := by rw [Category.assoc, hx, hh]
  have w₂ : (lam ≫ Z.φ) ≫ Z.G.hom = (A₁.A.hom ≫ M'.gp) ≫ h := by
    rw [hcomp.1.w, hyy, Category.assoc]
  let α : A₁.A.left ⟶ pullback Z.G.hom h := pullback.lift (lam ≫ Z.φ) (A₁.A.hom ≫ M'.gp) w₂
  have hα : IsGrpPullback A₁.A ((Over.pullback h).obj Z.G) M'.gp α :=
    IsGrpPullback.cancel (isGrpPullback_pullback Z.G h)
      (hcomp.congr hyy (pullback.lift_fst _ _ _).symm) (pullback.lift_snd _ _ _)
  refine ⟨α, hα, ?_⟩
  have hP := ρS.P.isLB
  have hZ := Z.L.isLB
  have i₁ : LBIso (ρS.P.L.pull φ) ((ρS.P.L.pull (pullback.fst ρS.P.A.hom Z.u₀)).pull lam) :=
    GlobalTheory.GenSpread.lbIso_pull_pull hP lam (pullback.lift_fst _ _ _).symm
  have i₂ : LBIso ((ρS.P.L.pull (pullback.fst ρS.P.A.hom Z.u₀)).pull lam) ((Z.L.L.pull Z.φ).pull lam) :=
    GlobalTheory.GenSpread.lbIso_pullback (LBIso.symm ⟨Z.w, Z.w_gen⟩) lam
  have i₃ : LBIso ((Z.L.L.pull Z.φ).pull lam) (Z.L.L.pull (lam ≫ Z.φ)) :=
    LBIso.symm (GlobalTheory.GenSpread.lbIso_pull_pull hZ lam rfl)
  have i₄ : LBIso (Z.L.L.pull (lam ≫ Z.φ)) ((Z.L.L.pull (pullback.fst Z.G.hom h)).pull α) :=
    GlobalTheory.GenSpread.lbIso_pull_pull hZ α (pullback.lift_fst _ _ _).symm
  have j₁ := LBIso.trans A₁.isLB (pull_isLB hP _) (pull_isLB (pull_isLB hP _) _) hlb i₁
  have j₂ := LBIso.trans A₁.isLB (pull_isLB (pull_isLB hP _) _) (pull_isLB (pull_isLB hZ _) _) j₁ i₂
  have j₃ := LBIso.trans A₁.isLB (pull_isLB (pull_isLB hZ _) _) (pull_isLB hZ _) j₂ i₃
  exact LBIso.trans A₁.isLB (pull_isLB hZ _) (pull_isLB (pull_isLB hZ _) _) j₃ i₄

end GlobalTheory.MumGen
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibrePulledSemiAbelianEqAbelianVarietyStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open Classical


theorem _root_.GlobalTheory.T.genericFibre_pulled_semiAbelian_eq_abelianVariety : ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [GlobalTheory.ZH.ArithBase o Ω] (S : GlobalTheory.ZH.ThetaSys o Ω) (ρS : S.Real) (M : GlobalTheory.ZH.RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), S.Over₀ M U₀ → ∀ (Z : GlobalTheory.ZH.ZHOut ρS M U₀ EE) (e : Ω →+* FractionRing R₁) (M' : Modif R₁) (h : M'.S ⟶ M.Z), M'.gp ≫ h = spMap e ≫ M.pt → ∀ (A₁ : PolAV (Sp (FractionRing R₁))) (φ : A₁.A.left ⟶ ρS.P.A.left), IsGrpPullback A₁.A ρS.P.A (spMap (e.comp S.R.val.toRingHom)) φ → LBIso A₁.L (ρS.P.L.pull φ) → ∃ α : A₁.A.left ⟶ ((Over.pullback h).obj Z.G).left, IsGrpPullback A₁.A ((Over.pullback h).obj Z.G) M'.gp α ∧ LBIso A₁.L ((Z.L.L.pull (pullback.fst Z.G.hom h)).pull α) := by
  first | exact @GlobalTheory.MumGen.genFibre_pullback | exact GlobalTheory.MumGen.genFibre_pullback | (intros; apply GlobalTheory.MumGen.genFibre_pullback <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisedCoverPullbackSemiAbelianModel

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open Classical

namespace GlobalTheory.Mum.CoverPull

theorem pt_mem_abLocus : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [GlobalTheory.ZH.ArithBase o Ω] (S : GlobalTheory.ZH.ThetaSys o Ω) (ρS : S.Real) (M : GlobalTheory.ZH.RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), S.Over₀ M U₀ → ∀ (Z : GlobalTheory.ZH.ZHOut ρS M U₀ EE) (w : Sp Ω), M.pt w ∈ abLocus Z.G := by
  intro o Ω _ _ _ _ S ρS M U₀ EE hO Z w
  haveI : IsProper ρS.P.A.hom := ρS.P.isAb.proper
  haveI : IsProper ((Over.pullback Z.u₀).obj ρS.P.A).hom := by
    show IsProper (pullback.snd ρS.P.A.hom Z.u₀)
    infer_instance
  refine GlobalTheory.range_subset_abLocus_of_isProper (G' := (Over.pullback Z.u₀).obj ρS.P.A) (f := U₀.ι) (φ := Z.φ) Z.semi Z.cart.1 ?_
  have hm : M.pt w ∈ U₀ := M.top_le_preimage_pt hO.ne (x := w) trivial
  exact ⟨⟨_, hm⟩, rfl⟩

theorem exists_unif_pullback : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : GlobalTheory.ZH.ThetaSys o Ω) (ρS : S.Real) (M : GlobalTheory.ZH.RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (Z : GlobalTheory.ZH.ZHOut ρS M U₀ EE) (T : Scheme.{0}) (h : T ⟶ M.Z) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ ξ : Sp W ⟶ T, ((ξ ≫ h) ⁻¹' abLocus Z.G).Nonempty → ∃ (G' : Over (Sp W)) (_ : GrpObj G') (_ : IsCommMonObj G') (β : G'.left ⟶ ((Over.pullback h).obj Z.G).left) (D' : DegData W (maximalIdeal W)) (A' : PolAV (Sp (FractionRing W))) (U' : Unif (maximalIdeal W) D' A' G'), IsGrpPullback G' ((Over.pullback h).obj Z.G) ξ β ∧ LBIso U'.LG.L ((Z.L.L.pull (pullback.fst Z.G.hom h)).pull β) := by
  intro o Ω _ _ _ S ρS M U₀ EE Z T h W _ _ _ hW ξ hab
  have pull_isLB : ∀ {X Y : Scheme.{0}} {L : LB X}, L.IsLB → ∀ F : Y ⟶ X, (L.pull F).IsLB := by
    intro X Y L hL F
    refine { cover := top_le_iff.1 ?_, g_self := ?_, cocycle := ?_ }
    · intro y _
      obtain ⟨i, hi⟩ := exists_chart hL (F y)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => i, mem_pull.2 hi⟩
    · intro J
      refine unit_ext fun y hy => ?_
      rw [gm_res (𝟙 Y) y _ hy, map_one, gm_pull_g L F (𝟙 Y) y J J hy hy]
      exact gm_self hL _ y (mem_pull.1 hy)
    · intro I J K
      refine unit_ext fun y hy => ?_
      rw [map_mul, gm_res (𝟙 Y) y _ hy, gm_res (𝟙 Y) y _ hy, gm_res (𝟙 Y) y _ hy, gm_pull_g L F (𝟙 Y) y I J hy.1.1 hy.1.2,
        gm_pull_g L F (𝟙 Y) y J K hy.1.2 hy.2, gm_pull_g L F (𝟙 Y) y I K hy.1.1 hy.2]
      exact gm_cocycle hL _ y (mem_pull.1 hy.1.1) (mem_pull.1 hy.1.2) (mem_pull.1 hy.2)
  obtain ⟨hdvr, hc, hch⟩ := (GlobalTheory.LN.cDvr_iff W).1 hW
  haveI := hch
  obtain ⟨D, A, U, hl, -⟩ := Z.unif W inferInstance inferInstance hc (ξ ≫ h) hab
  have hpt : (pullback.snd Z.G.hom (ξ ≫ h) ≫ ξ) ≫ h = pullback.snd Z.G.hom (ξ ≫ h) ≫ ξ ≫ h := Category.assoc _ _ _
  let β : pullback Z.G.hom (ξ ≫ h) ⟶ pullback Z.G.hom h :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ ξ) (pullback.condition.trans hpt.symm)
  have hβf : β ≫ pullback.fst Z.G.hom h = pullback.fst Z.G.hom (ξ ≫ h) := pullback.lift_fst _ _ _
  have hβs : β ≫ pullback.snd Z.G.hom h = pullback.snd Z.G.hom (ξ ≫ h) ≫ ξ := pullback.lift_snd _ _ _
  refine ⟨(Over.pullback (ξ ≫ h)).obj Z.G, inferInstance, inferInstance, β, D, A, U, ?_, ?_⟩
  · refine (isGrpPullback_pullback Z.G h).cancel ?_ hβs
    exact (isGrpPullback_pullback Z.G (ξ ≫ h)).congr rfl hβf.symm
  · exact LBIso.trans U.LG.isLB (pull_isLB Z.L.isLB _) (pull_isLB (pull_isLB Z.L.isLB _) _) hl
      (GlobalTheory.GenSpread.lbIso_pull_pull Z.L.isLB β hβf.symm)

end GlobalTheory.Mum.CoverPull

namespace GlobalTheory.Mum

theorem exists_uCover_of_zhOut : ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁] (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [GlobalTheory.ZH.ArithBase o Ω] (S : GlobalTheory.ZH.ThetaSys o Ω) (ρS : S.Real) (M : GlobalTheory.ZH.RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), S.Over₀ M U₀ → GlobalTheory.ZH.ZHOut ρS M U₀ EE → ∀ (b : o →+* R₁) (e : Ω →+* FractionRing R₁), (∀ x : o, e (algebraMap o Ω x) = algebraMap R₁ (FractionRing R₁) (b x)) → ∀ (A₁ : PolAV (Sp (FractionRing R₁))) (φ : A₁.A.left ⟶ ρS.P.A.left), IsGrpPullback A₁.A ρS.P.A (spMap (e.comp S.R.val.toRingHom)) φ → LBIso A₁.L (ρS.P.L.pull φ) → ∃ C : UCover R₁, C.A = A₁ := by
  intro R₁ _ _ _ o Ω _ _ _ _ S ρS M U₀ EE hO Z b e hb A₁ φ hcart hlb
  have pull_isLB : ∀ {X Y : Scheme.{0}} {L : LB X}, L.IsLB → ∀ F : Y ⟶ X, (L.pull F).IsLB := by
    intro X Y L hL F
    refine { cover := top_le_iff.1 ?_, g_self := ?_, cocycle := ?_ }
    · intro y _
      obtain ⟨i, hi⟩ := exists_chart hL (F y)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => i, mem_pull.2 hi⟩
    · intro J
      refine unit_ext fun y hy => ?_
      rw [gm_res (𝟙 Y) y _ hy, map_one, gm_pull_g L F (𝟙 Y) y J J hy hy]
      exact gm_self hL _ y (mem_pull.1 hy)
    · intro I J K
      refine unit_ext fun y hy => ?_
      rw [map_mul, gm_res (𝟙 Y) y _ hy, gm_res (𝟙 Y) y _ hy, gm_res (𝟙 Y) y _ hy, gm_pull_g L F (𝟙 Y) y I J hy.1.1 hy.1.2,
        gm_pull_g L F (𝟙 Y) y J K hy.1.2 hy.2, gm_pull_g L F (𝟙 Y) y I K hy.1.1 hy.2]
      exact gm_cocycle hL _ y (mem_pull.1 hy.1.1) (mem_pull.1 hy.1.2) (mem_pull.1 hy.2)
  have hs : IsProper M.s := GlobalTheory.SpreadAb.isProper_of_isProjOver hO.proj
  have hy : (spMap e ≫ M.pt) ≫ M.s = jK R₁ ≫ spMap b := by
    rw [Category.assoc, M.pt_s, jK, spMap, spMap, spMap, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext x
    exact hb x
  obtain ⟨M', h, hgp, -⟩ := GlobalTheory.T.exists_modification_closure_of_graph R₁ o b M.Z M.s hs _ hy
  obtain ⟨P₀, hP₀⟩ := GlobalTheory.T.exists_cubicalStructure_semiAbelianExtension o Ω S ρS M U₀ EE hO Z
  have hw : pullback.fst Z.G.hom h ≫ Z.G.hom = ((Over.pullback h).obj Z.G).hom ≫ h := pullback.condition
  have mul : ∀ (T : Over M'.S) (x y : T ⟶ (Over.pullback h).obj Z.G), toBase hw (x * y) = toBase hw x * toBase hw y := by
    intro T x y
    exact Over.OverMorphism.ext ((isGrpPullback_pullback Z.G h).2 T x y (toBase hw x) (toBase hw y) rfl rfl).symm
  obtain ⟨rig, hr, c, s, h₁, h₂, h₃, -⟩ := GlobalTheory.UU.exists_isCPMap P₀ mul _ (pull_isLB P₀.L.isLB _) _
    (GlobalTheory.UU.pullIso_isGen P₀.L.isLB _)
  obtain ⟨α, hα, hαl⟩ := GlobalTheory.T.genericFibre_pulled_semiAbelian_eq_abelianVariety R₁ o Ω S ρS M U₀ EE hO Z e M' h hgp A₁ φ hcart hlb
  refine ⟨{ toModif := M'
            G := (Over.pullback h).obj Z.G
            semi := by
              refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
              · have := Z.semi.comm; infer_instance
              · have := Z.semi.smooth; change Smooth (pullback.snd Z.G.hom h); infer_instance
              · have := Z.semi.separated; change IsSeparated (pullback.snd Z.G.hom h); infer_instance
              · have := Z.semi.quasiCompact; change QuasiCompact (pullback.snd Z.G.hom h); infer_instance
              · have := Z.semi.geomConnected; change GeometricallyConnected (pullback.snd Z.G.hom h); infer_instance
              · intro K _ _ q
                obtain ⟨E⟩ := Z.semi.fibres K (q ≫ h)
                let em : (Over.pullback (q ≫ h)).mapMon.obj (Mon.mk Z.G) ≅
                    (Over.pullback q).mapMon.obj ((Over.pullback h).mapMon.obj (Mon.mk Z.G)) :=
                  (Functor.mapMonNatIso (Over.pullbackComp q h) ≪≫ Functor.mapMonCompIso).app (Mon.mk Z.G)
                let e : (Over.pullback (q ≫ h)).obj Z.G ≅ (Over.pullback q).obj ((Over.pullback h).obj Z.G) :=
                  (Mon.forget _).mapIso em
                haveI : IsMonHom e.hom := by
                  show IsMonHom em.hom.hom
                  infer_instance
                haveI := E.grpB
                haveI := E.q_hom
                haveI := E.i_hom
                haveI : IsIso e.inv.left := Functor.map_isIso (Over.forget _) e.inv
                refine ⟨{ X := E.X
                          addCommGroup := E.addCommGroup
                          free := E.free
                          finite := E.finite
                          B := E.B
                          grpB := E.grpB
                          isAbelian := E.isAbelian
                          q := e.inv ≫ E.q
                          q_hom := inferInstance
                          q_flat := by rw [Over.comp_left]; have := E.q_flat; infer_instance
                          q_surjective := by rw [Over.comp_left]; have := E.q_surjective; infer_instance
                          q_quasiCompact := by rw [Over.comp_left]; have := E.q_quasiCompact; infer_instance
                          i := E.i ≫ e.hom
                          i_hom := inferInstance
                          isKernel := ?_ }⟩
                refine IsPullback.of_iso E.isKernel (Iso.refl _) e (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_ <;> simp
            P := ⟨⟨_, rig, pull_isLB P₀.L.isLB _, hr⟩, c, s, h₁, h₂, h₃⟩
            A := A₁
            α := α
            α_cart := hα
            α_lb := by
              show LBIso A₁.L ((P₀.L.L.pull (pullback.fst Z.G.hom h)).pull α)
              rw [hP₀]; exact hαl
            trait := ?_ }, rfl⟩
  intro W _ _ _ hW φW ξ hφ hξ
  obtain ⟨w, k, hk⟩ := GlobalTheory.T.exists_genericPoint_of_lies_over_generic R₁ M' W φW ξ hφ hξ
  have hab : ((ξ ≫ h) ⁻¹' abLocus Z.G).Nonempty := by
    refine ⟨w, ?_⟩
    have e1 : (ξ ≫ h) w = M.pt ((spMap e) k) := by
      rw [Scheme.Hom.comp_apply, hk, ← Scheme.Hom.comp_apply, hgp, Scheme.Hom.comp_apply]
    show (ξ ≫ h) w ∈ abLocus Z.G
    rw [e1]
    exact CoverPull.pt_mem_abLocus o Ω S ρS M U₀ EE hO Z _
  obtain ⟨G', iG, cG, β, D', A', U', hβ, hl⟩ := CoverPull.exists_unif_pullback o Ω S ρS M U₀ EE Z M'.S h W hW ξ hab
  have hid : spMap (RingHom.id W) ≫ ξ = ξ := by
    rw [spMap, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
  refine ⟨W, _, inferInstance, inferInstance, RingHom.id W, G', iG, cG, β, D', A', U', hW, Function.injective_id,
    RingHom.Finite.id W, hid.symm ▸ hβ, ?_⟩
  show LBIso U'.LG.L ((P₀.L.L.pull (pullback.fst Z.G.hom h)).pull β)
  rw [hP₀]; exact hl

end GlobalTheory.Mum
end
end
