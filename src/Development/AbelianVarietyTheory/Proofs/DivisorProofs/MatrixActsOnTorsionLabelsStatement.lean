module

public import Development.AbelianVarietyTheory.Definitions.Divisors.TorMatch
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsArBaseAway
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerEndomorphismLatticeAdjointStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerFormBundleMatricesAdjointStatement
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FunctorialOfUnif
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorsionClause
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformizationEndomorphismCalculus
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
import Development.AbelianVarietyTheory.Definitions.Divisors.SharpOverIff
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDegenerationEndomorphismOfAdmissibleBase
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.EndoLbIsoSymmetryHypothesisExtendNormalModel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoOfGenericNormalLocalBase
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Mathlib.Tactic.Linter.Style
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianHomExtensionHolds
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndomorphismMovesTorsionLatticeByAdjoint

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.EndLattice

open GlobalTheory.TorusExt

attribute [local instance] gtGroup

theorem congMod_y_of_end : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (E E' : GlobalTheory.UT.EndU U.toUnifPre), LBIso (cubeLB G ![fst G G ≫ E.aG, snd G G] U.LG.L) (cubeLB G ![fst G G, snd G G ≫ E'.aG] U.LG.L) → ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra (FractionRing R) K] (m : ℕ) (pk pk' : QkPt D.toPre K m) (x : TFK (R := R) K ⟶ A.A), 1 ≤ m → QkToAkU U.toUnifPre K m pk x → QkToAkU U.toUnifPre K m pk' (x ≫ E.aA) → CongMod m pk'.y (E'.h pk.y) := by
  intro R _ _ _ hBase G _ _ hG D A U E E' hE K _ _ _ m pk pk' x hm h1 h2
  haveI : CharZero R := hBase.2
  have hAdm := hBase.1
  obtain ⟨-, hFE⟩ := GlobalTheory.UT.functorial_of_unif R (maximalIdeal R) hAdm D A G hG U
  obtain ⟨-, hK⟩ := hFE E E' hE
  obtain ⟨hex, hiota, hmap⟩ := hK K
  have hcalc := (GlobalTheory.EndCalc.end_calculus GlobalTheory.firstFiveLaws R (maximalIdeal R) hAdm D A G hG U K E E E).2.1
  choose φ hφ using fun g => (hex g).exists
  have hadd : ∀ g g' : GtPtF D.toPre K, φ (g + g') = φ g + φ g' := fun g g' =>
    (isAdd_iff_eq _ _ _).1 (hcalc g g' (g + g') _ _ _ ((isAdd_iff_eq _ _ _).2 rfl) (hφ g) (hφ g') (hφ _))
  let φh : GtPtF D.toPre K →+ GtPtF D.toPre K :=
    AddMonoidHom.mk' φ hadd
  obtain ⟨h, hns, hio⟩ := pk.eq
  have hh : h = m • pk.g := (isNsmul_iff_eq _ _ _).1 hns
  let p' : QkPt D.toPre K m :=
    ⟨E'.h pk.y, φ pk.g, φ h, (isNsmul_iff_eq _ _ _).2 (by rw [hh]; exact map_nsmul φh m pk.g), hiota _ _ _ hio (hφ h)⟩
  have h3 : QkToAkU U.toUnifPre K m p' (x ≫ E.aA) := hmap m hm pk p' x rfl (hφ pk.g) h1
  obtain ⟨f, hf, -⟩ := GlobalTheory.TorsionIso.torsion_clause R (maximalIdeal R) hAdm D A G hG U K m hm
  have e : f p' = f pk' := ((hf.1 _ _).1 h3).symm.trans ((hf.1 _ _).1 h2)
  obtain ⟨z, hz, -⟩ := (hf.2.2.1 _ _).1 e
  exact ⟨z, hz⟩

end GlobalTheory.EndLattice
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndomorphismMovesTorsionLatticeByAdjointStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem _root_.GlobalTheory.T.endomorphism_moves_torsionLattice_by_adjoint : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (E E' : GlobalTheory.UT.EndU U.toUnifPre), LBIso (cubeLB G ![fst G G ≫ E.aG, snd G G] U.LG.L) (cubeLB G ![fst G G, snd G G ≫ E'.aG] U.LG.L) → ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra (FractionRing R) K] (m : ℕ) (pk pk' : QkPt D.toPre K m) (x : TFK (R := R) K ⟶ A.A), 1 ≤ m → QkToAkU U.toUnifPre K m pk x → QkToAkU U.toUnifPre K m pk' (x ≫ E.aA) → CongMod m pk'.y (E'.h pk.y) := by
  first | exact @GlobalTheory.EndLattice.congMod_y_of_end | exact GlobalTheory.EndLattice.congMod_y_of_end | (intros; apply GlobalTheory.EndLattice.congMod_y_of_end <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleAdjointOfGenericAdjoint

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.PoincAdj

open GlobalTheory.CechPic GlobalTheory.ZH.EndoExtend GlobalTheory.UT GlobalTheory.Mum.Two

theorem lbIso_adj_of_generic : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (E E' : GlobalTheory.UT.EndU U.toUnifPre), LBIso (cubeLB A.A ![fst A.A A.A ≫ E.aA, snd A.A A.A] A.L) (cubeLB A.A ![fst A.A A.A, snd A.A A.A ≫ E'.aA] A.L) → LBIso (cubeLB G ![fst G G ≫ E.aG, snd G G] U.LG.L) (cubeLB G ![fst G G, snd G G ≫ E'.aG] U.LG.L) := by
  intro R _ _ _ hB G _ _ hS D A U E E' hA
  have hR : AdmBase R (maximalIdeal R) := hB.1
  haveI : IsNoetherianRing R := hR.1
  haveI : IsIntegrallyClosed R := hR.2.2.1
  haveI := hS.smooth
  haveI := hS.geomConnected
  haveI := GlobalTheory.smooth_tensorObj_hom G G
  haveI := GlobalTheory.geometricallyIntegral_tensorObj_hom G G
  let U₁ := U.toUnifPre
  let δ := CartesianMonoidalCategory.prodComparison (Over.pullback (jK R)) G G
  let u := lift (fst ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G) ≫ U₁.gen.hom)
    (snd ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G) ≫ U₁.gen.hom)
  have hL := U₁.LG.isLB
  have hAL := A.isLB
  have hgen := U₁.gen_hom
  have hc' : CechPic.pull (pullback.fst G.hom (jK R)) (cls U₁.LG.L hL) =
      CechPic.pull U₁.gen.hom.left (cls A.L hAL) := by
    obtain ⟨w, hw⟩ := U₁.ext
    rw [← cls_pull hL _ (pull_isLB hL _), ← cls_pull hAL _ (pull_isLB hAL _)]
    exact ((cls_eq_iff _ _).2 ⟨w, hw⟩).symm
  have Aw : ∀ {Y Z : Over (Sp R)} (q : Y ⟶ Z),
      ((Over.pullback (jK R)).map q).left ≫ pullback.fst Z.hom (jK R) = pullback.fst Y.hom (jK R) ≫ q.left :=
    fun q => pullback.lift_fst _ _ _
  have hu : u.left ≫ (A.A ⊗ A.A).hom =
      ((Over.pullback (jK R)).obj G ⊗ (Over.pullback (jK R)).obj G).hom ≫ 𝟙 _ := by
    rw [Category.comp_id]; exact Over.w u
  have key : ∀ (x y : G ⟶ G) (cx cy : A.A ⟶ A.A), Gen₀ U₁ U₁ x cx → Gen₀ U₁ U₁ y cy →
      CechPic.pull (pullback.fst (G ⊗ G).hom (jK R)) (cubeCls G ![fst G G ≫ x, snd G G ≫ y] (cls U₁.LG.L hL)) =
        CechPic.pull δ.left (CechPic.pull u.left
          (cubeCls A.A ![fst A.A A.A ≫ cx, snd A.A A.A ≫ cy] (cls A.L hAL))) := by
    intro x y cx cy hx hy
    have e' := push_cubeCls (isGrpPullback_pullback G (jK R)) (T' := (Over.pullback (jK R)).obj (G ⊗ G))
      (T := G ⊗ G) (fun i => (Over.pullback (jK R)).map (![fst G G ≫ x, snd G G ≫ y] i))
      ![fst G G ≫ x, snd G G ≫ y] (pullback.fst (G ⊗ G).hom (jK R)) pullback.condition
      (fun i => Aw _) (cls U₁.LG.L hL)
    refine e'.trans ((pull_cubeCls _ ![fst _ _ ≫ (Over.pullback (jK R)).map x,
      snd _ _ ≫ (Over.pullback (jK R)).map y] _ δ (fun i => ?_) _).symm.trans ?_)
    · fin_cases i <;> simp [δ]
    rw [hc']
    refine congrArg (CechPic.pull δ.left) (push_cubeCls (isGrpPullback_of_iso U₁.gen) _ _ u.left hu (fun i => ?_) _).symm
    fin_cases i
    · show ((fst _ _ ≫ (Over.pullback (jK R)).map x) ≫ U₁.gen.hom).left = (u ≫ fst A.A A.A ≫ cx).left
      congr 1
      simp only [u, Category.assoc, lift_fst_assoc]
      rw [hx]
    · show ((snd _ _ ≫ (Over.pullback (jK R)).map y) ≫ U₁.gen.hom).left = (u ≫ snd A.A A.A ≫ cy).left
      congr 1
      simp only [u, Category.assoc, lift_snd_assoc]
      rw [hy]
  have g₁ : Gen₀ U₁ U₁ (𝟙 G) (𝟙 A.A) := by
    unfold Gen₀; rw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  have k₁ := key E.aG (𝟙 G) E.aA (𝟙 A.A) E.ext g₁
  have k₂ := key (𝟙 G) E'.aG (𝟙 A.A) E'.aA g₁ E'.ext
  simp only [Category.comp_id] at k₁ k₂
  have eA : cubeCls A.A ![fst A.A A.A ≫ E.aA, snd A.A A.A] (cls _ hAL) =
      cubeCls A.A ![fst A.A A.A, snd A.A A.A ≫ E'.aA] (cls _ hAL) :=
    (cls_cubeLB A.A _ hAL).symm.trans (((cls_eq_iff _ _).2 hA).trans (cls_cubeLB A.A _ hAL))
  refine GlobalTheory.Mum.lbIso_of_generic_local R (G ⊗ G) (η[G ⊗ G]).left (Over.w _) _ _ (LB.isLB_linComb hL _ _)
    (LB.isLB_linComb hL _ _) ?_
  refine (cls_eq_iff (pull_isLB (LB.isLB_linComb hL _ _) _) (pull_isLB (LB.isLB_linComb hL _ _) _)).1 ?_
  rw [cls_pull (LB.isLB_linComb hL _ _) _ (pull_isLB (LB.isLB_linComb hL _ _) _),
    cls_pull (LB.isLB_linComb hL _ _) _ (pull_isLB (LB.isLB_linComb hL _ _) _)]
  refine (congrArg (CechPic.pull _) (cls_cubeLB G ![fst G G ≫ E.aG, snd G G] hL)).trans ?_
  refine Eq.trans ?_ (congrArg (CechPic.pull _) (cls_cubeLB G ![fst G G, snd G G ≫ E'.aG] hL)).symm
  rw [k₁, k₂, eA]

end GlobalTheory.PoincAdj
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleAdjointOfGenericAdjointStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem _root_.GlobalTheory.T.mumfordBundle_adjoint_of_generic_adjoint : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (E E' : GlobalTheory.UT.EndU U.toUnifPre), LBIso (cubeLB A.A ![fst A.A A.A ≫ E.aA, snd A.A A.A] A.L) (cubeLB A.A ![fst A.A A.A, snd A.A A.A ≫ E'.aA] A.L) → LBIso (cubeLB G ![fst G G ≫ E.aG, snd G G] U.LG.L) (cubeLB G ![fst G G, snd G G ≫ E'.aG] U.LG.L) := by
  first | exact @GlobalTheory.PoincAdj.lbIso_adj_of_generic | exact GlobalTheory.PoincAdj.lbIso_adj_of_generic | (intros; apply GlobalTheory.PoincAdj.lbIso_adj_of_generic <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixActsOnTorsionLabels

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.Poinc.Eq8.MatTors

theorem endU_exists (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (hadm : AdmBase R (maximalIdeal R))
    (D : DegData R (maximalIdeal R)) (P : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G]
    (hG : IsSemiAbelian G) (U : Unif (maximalIdeal R) D P G) (aA : P.A ⟶ P.A) (haA : IsMonHom aA) :
    ∃ E : GlobalTheory.UT.EndU U.toUnifPre, E.aA = aA := by
  haveI := hadm.1
  haveI := hadm.2.2.1
  have := U.gen_hom
  have hinv : IsMonHom U.gen.inv := inferInstance
  obtain ⟨F, ⟨hF, hF'⟩, -⟩ := GlobalTheory.Published.SemiAbelianHomExtension.fractionField GlobalTheory.semiAbelianHomExtension_holds R
    (FractionRing R) G G hG hG (U.gen.hom ≫ aA ≫ U.gen.inv)
  obtain ⟨E, -, hE⟩ := GlobalTheory.UT.exists_degenerationEndomorphism_of_admissibleBase R (maximalIdeal R) hadm D P G hG U F aA hF haA
    (by rw [hF']; simp)
  exact ⟨E, hE⟩

theorem isMonHom_matrix (S : Scheme.{0}) (X Y : Over S) [GrpObj X] [GrpObj Y] [IsCommMonObj Y] (pr : Fin 8 → (X ⟶ Y))
    (hpr : ∀ a, IsMonHom (pr a))
    (hu : ∀ (T' : Over S) (y' : Fin 8 → (T' ⟶ Y)), ∃! x : T' ⟶ X, ∀ a, x ≫ pr a = y' a) (f : X ⟶ X)
    (a : Matrix (Fin 8) (Fin 8) ℤ) (hf : ∀ u, f ≫ pr u = (List.ofFn fun v => pr v ^ a u v).prod) : IsMonHom f := by
  haveI : ∀ v, IsMonHom (pr v) := hpr
  refine ReciprocityTheory.ChartRestriction.G.Geo.Tor.isMonHom_of_mul f fun T x y => ?_
  have hz : ∀ (z : T ⟶ X) (u : Fin 8), z ≫ f ≫ pr u = ∏ v, (z ≫ pr v) ^ a u v := by
    intro z u
    let φz : (X ⟶ Y) →* (T ⟶ Y) := ⟨⟨(z ≫ ·), MonObj.comp_one z⟩, MonObj.comp_mul z⟩
    rw [hf u, List.prod_ofFn]
    exact (map_prod φz _ _).trans (Finset.prod_congr rfl fun v _ => map_zpow φz _ _)
  refine (hu T fun u => ((x * y) ≫ f) ≫ pr u).unique (fun u => rfl) (fun u => ?_)
  rw [MonObj.mul_comp, Category.assoc, Category.assoc, Category.assoc, hz, hz, hz]
  simp only [MonObj.mul_comp, mul_zpow, Finset.prod_mul_distrib]

theorem exists_adjoint (S a : Matrix (Fin 8) (Fin 8) ℤ) (hS : S.det = 1) : ∃ a', S * a' = a.transpose * S :=
  ⟨S⁻¹ * (a.transpose * S), Matrix.mul_nonsing_inv_cancel_left S _ (hS ▸ isUnit_one)⟩

theorem matrix_acts_on_torsion_labels : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → IsDiscreteValuationRing R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (D' : DegData R (maximalIdeal R)) (A' : PolAV (Sp (FractionRing R))) (U' : Unif (maximalIdeal R) D' A' G') (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (pr : Fin 8 → (A'.A ⟶ A.A)), (∀ a, IsMonHom (pr a)) → (∀ (T' : Over (Sp (FractionRing R))) (y : Fin 8 → (T' ⟶ A.A)), ∃! z : T' ⟶ A'.A, ∀ a, z ≫ pr a = y a) → LBIso A'.L (LB.LinComb (abelian₂ A.A A.L) (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left) (fun ab => W ab.1 ab.2)) → ∀ (pG : Fin 8 → (G' ⟶ G)), (∀ v, IsMonHom (pG v)) → (∀ v, (Over.pullback (jK R)).map (pG v) ≫ U.gen.hom = U'.gen.hom ≫ pr v) → ∀ (c : Fin 8 → (D.toPre.X →+ D'.toPre.X)), (∀ v, TorMatch U U' (RingHom.id R) (pG v).left (c v)) → ∀ e : D'.toPre.X ≃+ (Fin 8 → D.toPre.X), (∀ y, ∑ v, c v (∑ u, (W + W.transpose) v u • e y u) = y) → ∀ (a : Matrix (Fin 8) (Fin 8) ℤ) (f : A'.A ⟶ A'.A), (∀ u, f ≫ pr u = (List.ofFn fun v => pr v ^ a u v).prod) → ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra (FractionRing R) K] (m : ℕ) (pk pk' : QkPt D'.toPre K m) (x : TFK (R := R) K ⟶ A'.A), 1 ≤ m → QkToAkU U'.toUnifPre K m pk x → QkToAkU U'.toUnifPre K m pk' (x ≫ f) → CongMod m (e pk'.y) (fun u => ∑ v, a u v • e pk.y v) := by
  intro R _ _ _ hB hdvr G _ _ hG D A U G' _ _ hG' D' A' U' W hW pr hpr hpu hL pG hpG hext c hc e he a f hf K _ _ _ m pk pk' x
    hm hx hx'
  obtain ⟨a', ha⟩ := exists_adjoint (W + W.transpose) a hW.2
  obtain ⟨f', hf', -⟩ := hpu A'.A (fun u => (List.ofFn fun v => pr v ^ a' u v).prod)
  obtain ⟨E, hE⟩ := endU_exists R hB.1 D' A' G' hG' U' f (isMonHom_matrix _ A'.A A.A pr hpr hpu f a hf)
  obtain ⟨E', hE'⟩ := endU_exists R hB.1 D' A' G' hG' U' f' (isMonHom_matrix _ A'.A A.A pr hpr hpu f' a' hf')
  subst hE hE'
  have h₁ := GlobalTheory.T.eighthPower_formBundle_matrices_adjoint _ A A' W pr hpr hL a a' ha E.aA E'.aA hf hf'
  have h₂ := GlobalTheory.T.mumfordBundle_adjoint_of_generic_adjoint R hB G' hG' D' A' U' E E' h₁
  obtain ⟨w, hw⟩ := GlobalTheory.T.endomorphism_moves_torsionLattice_by_adjoint R hB G' hG' D' A' U' E E' h₂ K m pk pk' x hm hx hx'
  have h₃ := GlobalTheory.T.eighth_power_endomorphism_lattice_adjoint R hB hdvr G hG D A U G' hG' D' A' U' W hW pr hpr hpu hL pG hpG hext c hc e he a a' ha E' hf' pk.y
  exact ⟨e w, by rw [hw, map_add (f := _), map_nsmul, h₃]⟩

end GlobalTheory.Poinc.Eq8.MatTors
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixActsOnTorsionLabelsStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem _root_.GlobalTheory.T.matrix_acts_on_torsion_labels_alt : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → IsDiscreteValuationRing R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (D' : DegData R (maximalIdeal R)) (A' : PolAV (Sp (FractionRing R))) (U' : Unif (maximalIdeal R) D' A' G') (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (pr : Fin 8 → (A'.A ⟶ A.A)), (∀ a, IsMonHom (pr a)) → (∀ (T' : Over (Sp (FractionRing R))) (y : Fin 8 → (T' ⟶ A.A)), ∃! z : T' ⟶ A'.A, ∀ a, z ≫ pr a = y a) → LBIso A'.L (LB.LinComb (abelian₂ A.A A.L) (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left) (fun ab => W ab.1 ab.2)) → ∀ (pG : Fin 8 → (G' ⟶ G)), (∀ v, IsMonHom (pG v)) → (∀ v, (Over.pullback (jK R)).map (pG v) ≫ U.gen.hom = U'.gen.hom ≫ pr v) → ∀ (c : Fin 8 → (D.toPre.X →+ D'.toPre.X)), (∀ v, TorMatch U U' (RingHom.id R) (pG v).left (c v)) → ∀ e : D'.toPre.X ≃+ (Fin 8 → D.toPre.X), (∀ y, ∑ v, c v (∑ u, (W + W.transpose) v u • e y u) = y) → ∀ (a : Matrix (Fin 8) (Fin 8) ℤ) (f : A'.A ⟶ A'.A), (∀ u, f ≫ pr u = (List.ofFn fun v => pr v ^ a u v).prod) → ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra (FractionRing R) K] (m : ℕ) (pk pk' : QkPt D'.toPre K m) (x : TFK (R := R) K ⟶ A'.A), 1 ≤ m → QkToAkU U'.toUnifPre K m pk x → QkToAkU U'.toUnifPre K m pk' (x ≫ f) → CongMod m (e pk'.y) (fun u => ∑ v, a u v • e pk.y v) := by
  first | exact @GlobalTheory.Poinc.Eq8.MatTors.matrix_acts_on_torsion_labels | exact GlobalTheory.Poinc.Eq8.MatTors.matrix_acts_on_torsion_labels | (intros; apply GlobalTheory.Poinc.Eq8.MatTors.matrix_acts_on_torsion_labels <;> assumption)
end
end
