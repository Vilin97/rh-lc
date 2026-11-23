module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeGlobalOneFormsClosedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeOneFormFrameAndSquareStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocycleOneFormsCoboundaryOfRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPairBelowTwo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormPowSmulEqZeroOfResBasicOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocalizationOfData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairCoverAffine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoFormExistsPowSmulEqZeroOfIsLocalization
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
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivativeCurvatureClosednessRelationsAddStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConnectionSumWedgeCurvatureAbelianSchemeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveH1StructureAbelianStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumWedgePrimitiveOneFormsEqZeroAbelianSchemeStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectionCurvatureSumWedgeSemilinearPullback

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

section Helpers

variable {R R' : Type} [CommRing R] [CommRing R'] {C C' : Type} [Category.{0} C] [Category.{0} C']

theorem pOm_wsum (F : C ⥤ CommAlgCat.{0} R) {n : ℕ} (u v : Fin n → Glob1 F) {T T' : C} (w : T ⟶ T') :
    pOm F 2 w (wsum F u v T) = wsum F u v T' := by
  unfold wsum

  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [pOm_wedge, ← (u k).2 w, ← (v k).2 w]

theorem qOm_wsum {σ : R →+* R'} {F : C ⥤ CommAlgCat.{0} R} {F' : C' ⥤ CommAlgCat.{0} R'} (m : CoefMap σ F F')
    {n : ℕ} (u v : Fin n → Glob1 F) (T : C') :
    qOm m 2 T (wsum F u v (m.G.obj T)) =
      wsum F' (fun k ↦ pullGlob1 m (u k)) (fun k ↦ pullGlob1 m (v k)) T := by
  unfold wsum

  rw [map_sum]
  exact Finset.sum_congr rfl fun k _ ↦ qOm_wedge m _ _

end Helpers

end GlobalTheory.AbCoh

namespace GlobalTheory.AbCoh

theorem obRel_pullHO1 : ∀ (R R' : Type) [CommRing R] [CommRing R'] (X X' : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (σ : R →+* R') (φ : X' ⟶ X) (h : φ ≫ s = s' ≫ spMap σ) (x : HO1 s) (n : ℕ) (u v : Fin n → GlobForm s), ObRel (OAff s) x u v → ObRel (OAff s') (pullHO1 h x) (fun k ↦ GlobalTheory.CechDR.pullForm h (u k)) (fun k ↦ GlobalTheory.CechDR.pullForm h (v k)) := by
  intro R R' _ _ X X' s s' σ φ h x n u v hx
  obtain ⟨f, ω, hfx, hconn, hcurv⟩ := hx
  obtain ⟨f', hf'⟩ := H1.mk_surjective (OAff s') (pullHO1 h x)
  have e1 := isPullO_pullHO1 h x
  rw [IsPullO, ← hf', ← hfx, CoefMap.pullCohomologyOne_class, CoefMap.pullCohomologyOne_class, H1.mk_eq_mk] at e1
  obtain ⟨b, hb⟩ := e1
  have hb' : ∀ (t t' : (Pair φ)ᵒᵖ) (a : t ⟶ t'), ((pairRes φ s').pullbackOneCocycle f').1 t t' a =
      ((pairPull h).pullbackOneCocycle f).1 t t' a - (b t' - mp (OPair φ s') a (b t)) := by
    intro t t' a
    have e := congrFun (congrFun (congrFun hb t) t') a
    simp only [Pi.sub_apply, amitsur_d0_apply] at e
    linear_combination e
  let ω'' : ∀ t : (Pair φ)ᵒᵖ, Ω[(OAff s').obj ((pairFst φ).obj t)⁄R'] :=
    fun t ↦ q1 (pairPull h) t (ω _) - D R' _ (b t)
  let κ : A1 (OAff s') := fun T T' ψ ↦ D R' _ (f'.1 T T' ψ)
  have hκ : ∀ ⦃T T' T'' : AffOp X'⦄ (a : T ⟶ T') (c : T' ⟶ T''),
      κ T T'' (a ≫ c) = p1 (OAff s') c (κ T T' a) + κ T' T'' c := by
    intro T T' T'' a c
    simp only [κ]
    rw [Z1.comp f', map_add (f := _), p1_D]
  have hθ' : ∀ ⦃t t' : (Pair φ)ᵒᵖ⦄ (a : t ⟶ t'),
      κ _ _ ((pairFst φ).map a) = ω'' t' - p1 (OAff s') ((pairFst φ).map a) (ω'' t) := by
    intro t t' a
    have e0 := hconn ((pairSnd φ).map a)
    have e : q1 (pairPull h) t' (ω _) = p1 (OPair φ s') a (q1 (pairPull h) t (ω _)) +
        D R' _ ((pairPull h).α t' (f.1 _ _ ((pairSnd φ).map a))) := by
      rw [← cechDeRhamCoefMapOneForms_naturality, ← cechDeRhamCoefMapOneForms_D, ← map_add (f := _)]; exact congrArg _ e0
    have k1 : κ _ _ ((pairFst φ).map a) = D R' _ (((pairPull h).pullbackOneCocycle f).1 t t' a) -
        (D R' _ (b t') - D R' _ (mp (OPair φ s') a (b t))) := by
      simp only [κ]
      rw [show f'.1 _ _ ((pairFst φ).map a) = ((pairRes φ s').pullbackOneCocycle f').1 t t' a from rfl, hb' t t' a,
        map_sub, map_sub] <;> rfl
    have k3 : p1 (OPair φ s') a (D R' _ (b t)) = D R' _ (mp (OPair φ s') a (b t)) :=
      p1_D _ _ _
    have key : ∀ {M : Type} [AddCommGroup M] (df da db dm q' q pq pd : M), df = da - (db - dm) →
        q' = pq + da → pd = dm → df = (q' - db) - (pq - pd) := by
      intros; subst_vars; abel
    rw [show ω'' t' - p1 (OAff s') ((pairFst φ).map a) (ω'' t) = (q1 (pairPull h) t' (ω _) - D R' _ (b t')) -
      (p1 (OPair φ s') a (q1 (pairPull h) t (ω _)) -
        p1 (OPair φ s') a (D R' _ (b t))) from by simp only [ω'', map_sub] <;> rfl]
    exact key _ _ _ _ _ (0 : Ω[(OAff s').obj ((pairFst φ).obj t')⁄R']) _ _ k1 e k3
  have hcov := _root_.GlobalTheory.CechDR.pair_cover_affine φ s'
  have hdir := _root_.GlobalTheory.CechDR.exists_pair_below_two φ s'
  have hs1 := _root_.GlobalTheory.CechDR.form_eq_zero_of_basis_cover s' (pairFst φ) hcov
  have hg1 := _root_.GlobalTheory.CechDR.FormExt.glue_one_forms s' (pairFst φ) hcov hdir
  have hs2 := _root_.GlobalTheory.CechDR.twoForm_sep_of_basis s' (pairFst φ) hcov
  obtain ⟨θ, hθ⟩ := _root_.GlobalTheory.cocycle_one_forms_coboundary_of_restrict (OAff s') (pairFst φ) hs1 hg1
    κ hκ ω'' hθ'
  have key2 : ∀ {M : Type} [AddCommGroup M] (k A PA C PC PAC : M), k = A - PA → k = C - PC →
      PAC = PA - PC → A - C = PAC := by
    intro M _ k A PA C PC PAC h1 h2 h3
    subst h3
    exact sub_eq_sub_iff_sub_eq_sub.1 (h1.symm.trans h2)
  let δ : Glob1 (OPair φ s') := ⟨fun t ↦ θ ((pairFst φ).obj t) - ω'' t, fun t t' a ↦
    key2 _ _ _ _ _ _ (hθ ((pairFst φ).map a)) (hθ' a) (map_sub _ _ _)⟩
  obtain ⟨β, hβ⟩ := (pairRes_bijective φ s').2.1.2 δ
  have hβt : ∀ t, β.1 ((pairFst φ).obj t) = θ ((pairFst φ).obj t) - ω'' t := fun t ↦
    (cechDeRhamCoefMapOneForms_restrictAlongFunctor (OAff s') (pairFst φ) t _).symm.trans (congrArg (fun z : Glob1 (OPair φ s') ↦ z.1 t) hβ)
  refine ⟨f', fun T ↦ θ T - β.1 T, hf', fun T T' ψ ↦ ?_, fun T ↦ ?_⟩
  · have key3 : ∀ {M : Type} [AddCommGroup M] (k A PA B PB : M), k = A - PA → B = PB →
        A - B = (PA - PB) + k := by
      intros; subst_vars; abel
    rw [map_sub]
    exact key3 _ _ _ _ _ (hθ ψ) (β.2 ψ)
  · refine sub_eq_zero.1 (hs2 T _ fun t w ↦ ?_)
    have key4 : ∀ {M : Type} [AddCommGroup M] (k A PA B PB O : M), k = A - PA → B = PB → B = A - O →
        PA - PB = O - k := by
      intros; subst_vars; abel
    have key5 : ∀ (B : Type) [CommRing B] [Algebra R' B] (y : Ω[B⁄R']) (c : B),
        dOne R' B (y - D R' B c) = dOne R' B y := fun B _ _ y c ↦ by rw [map_sub, dOne_D, sub_zero]
    have c1 : p1 (OAff s') w (θ T - β.1 T) = ω'' t - D R' _ (f'.1 _ _ w) := by
      rw [map_sub]; exact key4 _ _ _ _ _ _ (hθ w) (β.2 w) (hβt t)
    have e1 : ∀ (z : Fin n → GlobForm s) k, pullGlob1 (pairPull h) (z k) =
        pullGlob1 (pairRes φ s') (GlobalTheory.CechDR.pullForm h (z k)) := fun z k ↦ isPullForm_pullForm h (z k)
    have c2 : dOne R' ((OAff s').obj ((pairFst φ).obj t)) (ω'' t) = wsum (OAff s')
        (fun k ↦ GlobalTheory.CechDR.pullForm h (u k)) (fun k ↦ GlobalTheory.CechDR.pullForm h (v k)) ((pairFst φ).obj t) := by
      calc dOne R' ((OAff s').obj ((pairFst φ).obj t)) (ω'' t)
          = dOne R' ((OPair φ s').obj t) (q1 (pairPull h) t (ω ((pairSnd φ).obj t))) := key5 _ _ _
        _ = qOm (pairPull h) 2 t (dOne R ((OAff s).obj ((pairSnd φ).obj t)) (ω ((pairSnd φ).obj t))) :=
          (qOm_dOne _ _).symm
        _ = qOm (pairPull h) 2 t (wsum (OAff s) u v ((pairSnd φ).obj t)) := by rw [hcurv]
        _ = wsum (OPair φ s') (fun k ↦ pullGlob1 (pairPull h) (u k)) (fun k ↦ pullGlob1 (pairPull h) (v k)) t :=
          qOm_wsum _ _ _ _
        _ = wsum (OPair φ s') (fun k ↦ pullGlob1 (pairRes φ s') (GlobalTheory.CechDR.pullForm h (u k)))
            (fun k ↦ pullGlob1 (pairRes φ s') (GlobalTheory.CechDR.pullForm h (v k))) t := by
          simp only [e1 u, e1 v]
        _ = qOm (pairRes φ s') 2 t (wsum (OAff s') (fun k ↦ GlobalTheory.CechDR.pullForm h (u k))
            (fun k ↦ GlobalTheory.CechDR.pullForm h (v k)) ((pairFst φ).obj t)) := (qOm_wsum _ _ _ _).symm
        _ = _ := qOm_restrict _ _ _ _
    have c3 := pOm_wsum (OAff s') (fun k ↦ GlobalTheory.CechDR.pullForm h (u k))
      (fun k ↦ GlobalTheory.CechDR.pullForm h (v k)) w
    rw [map_sub, pOm_dOne, c1, c3, key5, c2, sub_self]

end GlobalTheory.AbCoh
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectionCurvatureSumWedgeSemilinearPullbackStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.connectionCurvatureSumWedge_semilinearPullback : ∀ (R R' : Type) [CommRing R] [CommRing R'] (X X' : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (σ : R →+* R') (φ : X' ⟶ X) (h : φ ≫ s = s' ≫ spMap σ) (x : HO1 s) (n : ℕ) (u v : Fin n → GlobForm s), ObRel (OAff s) x u v → ObRel (OAff s') (pullHO1 h x) (fun k ↦ GlobalTheory.CechDR.pullForm h (u k)) (fun k ↦ GlobalTheory.CechDR.pullForm h (v k)) := by
  first | exact @GlobalTheory.AbCoh.obRel_pullHO1 | exact GlobalTheory.AbCoh.obRel_pullHO1 | (intros; apply GlobalTheory.AbCoh.obRel_pullHO1 <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurvatureSumWedgeWellDefinedAndDeRhamLift

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AbCoh

theorem curvature_wellDefined_and_lift : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R), (Closed1 F = ⊤ → ∀ (x : GlobalTheory.CatCoh.H1 F) (n n' : ℕ) (u v : Fin n → Glob1 F) (u' v' : Fin n' → Glob1 F), ObRel F x u v → ObRel F x u' v' → wsum F u v = wsum F u' v') ∧ ∀ (x : GlobalTheory.CatCoh.H1 F) (n : ℕ) (u v : Fin n → Glob1 F), ObRel F x u v → wsum F u v = 0 → ∃ c, toO F c = x := by
  intro R _ C _ F
  refine ⟨fun hcl x n n' u v u' v' ⟨f, ω, hf, hω, hd⟩ ⟨f', ω', hf', hω', hd'⟩ ↦ ?_,
    fun x n u v ⟨f, ω, hf, hω, hd⟩ h0 ↦ ?_⟩
  · obtain ⟨b, hb⟩ := H1.mk_eq_mk.1 (hf.trans hf'.symm)
    let e0 : Glob1 F := ⟨fun T ↦ ω T - ω' T - D R _ (b T), fun T T' φ ↦ by
      have hb' : f.1 T T' φ - f'.1 T T' φ = b T' - mp F φ (b T) :=
        (congrFun (congrFun (congrFun hb T) T') φ).symm
      have h2 : D R _ (b T') = D R _ (f.1 T T' φ) - D R _ (f'.1 T T' φ) + D R _ (mp F φ (b T)) := by
        rw [← map_sub, hb', map_sub]; abel
      show ω T' - ω' T' - D R _ (b T') = p1 F φ (ω T - ω' T - D R _ (b T))
      rw [hω φ, hω' φ, map_sub, map_sub, p1_D, h2]
      abel⟩
    have he0 : e0 ∈ Closed1 F := by rw [hcl]; exact Submodule.mem_top
    funext T
    rw [← hd T, ← hd' T]
    have h := he0 T
    change dOne R _ (ω T - ω' T - D R _ (b T)) = 0 at h
    rw [map_sub, map_sub, dOne_D, sub_zero, sub_eq_zero] at h
    exact h
  · refine ⟨Hyp1.mk F ⟨(f.1, ω), mem_cechDeRhamTotalCocyclesOne_iff.2 ⟨f.2, hω, fun T ↦ (hd T).trans (congrFun h0 T)⟩⟩, ?_⟩
    rw [toO_mk]
    exact hf

end GlobalTheory.AbCoh
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurvatureSumWedgeWellDefinedAndDeRhamLiftStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.curvatureSumWedge_wellDefined_and_deRhamLift : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R), (Closed1 F = ⊤ → ∀ (x : GlobalTheory.CatCoh.H1 F) (n n' : ℕ) (u v : Fin n → Glob1 F) (u' v' : Fin n' → Glob1 F), ObRel F x u v → ObRel F x u' v' → wsum F u v = wsum F u' v') ∧ ∀ (x : GlobalTheory.CatCoh.H1 F) (n : ℕ) (u v : Fin n → Glob1 F), ObRel F x u v → wsum F u v = 0 → ∃ c, toO F c = x := by
  first | exact @GlobalTheory.AbCoh.curvature_wellDefined_and_lift | exact GlobalTheory.AbCoh.curvature_wellDefined_and_lift | (intros; apply GlobalTheory.AbCoh.curvature_wellDefined_and_lift <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamToStructureH1Surjective

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.AbCoh

theorem wsum_append {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)
    {n n' : ℕ} (u v : Fin n → Glob1 F) (u' v' : Fin n' → Glob1 F) :
    wsum F (Fin.append u u') (Fin.append v v') = wsum F u v + wsum F u' v' := by
  funext T
  simp only [wsum, Fin.sum_univ_add, Fin.append_left, Fin.append_right, Pi.add_apply]

theorem toHO1_surjective : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A →
    SmoothOfRelativeDimension g A.hom → Function.Surjective (toHO1 A.hom) := by
  intro R _ A _ g hA hg x
  obtain ⟨m, u, v, hx⟩ := GlobalTheory.T.exists_connection_sumWedgeCurvature_abelianScheme R A g hA hg x
  obtain ⟨-, -, hAA, hgAA⟩ := GlobalTheory.T.abelianScheme_oneFormFrame_and_square R A g hA hg
  have hcl : Closed1 (OAff (A ⊗ A).hom) = ⊤ := GlobalTheory.T.abelianScheme_globalOneForms_closed R (A ⊗ A) (g + g) hAA hgAA
  have hμ := GlobalTheory.T.connectionCurvatureSumWedge_semilinearPullback R R _ _ A.hom (A ⊗ A).hom (RingHom.id R) (μ[A]).left (ovw μ[A]) x m u v hx
  have h1 := GlobalTheory.T.connectionCurvatureSumWedge_semilinearPullback R R _ _ A.hom (A ⊗ A).hom (RingHom.id R) (fst A A).left (ovw (fst A A)) x m u v hx
  have h2 := GlobalTheory.T.connectionCurvatureSumWedge_semilinearPullback R R _ _ A.hom (A ⊗ A).hom (RingHom.id R) (snd A A).left (ovw (snd A A)) x m u v hx
  have hsum := (GlobalTheory.T.derivativeCurvatureClosedness_relations_add R _ (OAff (A ⊗ A).hom)).2.1 _ _ m m _ _ _ _ h1 h2
  have hprim : pullHO1 (ovw μ[A]) x = pullHO1 (ovw (fst A A)) x + pullHO1 (ovw (snd A A)) x :=
    GlobalTheory.T.primitive_h1_structure_abelian R A g hA hg x
  rw [← hprim] at hsum
  have heq := (GlobalTheory.T.curvatureSumWedge_wellDefined_and_deRhamLift R _ (OAff (A ⊗ A).hom)).1 hcl _ m (m + m) _ _ _ _ hμ hsum
  rw [wsum_append] at heq
  have h0 : wsum (OAff A.hom) u v = 0 := GlobalTheory.T.sum_wedge_primitive_oneForms_eq_zero_abelianScheme R A g hA hg m u v heq
  exact (GlobalTheory.T.curvatureSumWedge_wellDefined_and_deRhamLift R _ (OAff A.hom)).2 x m u v hx h0

end GlobalTheory.AbCoh
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamToStructureH1SurjectiveStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.de_rham_to_structure_h1_surjective : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → Function.Surjective (toHO1 A.hom) := by
  first | exact @GlobalTheory.AbCoh.toHO1_surjective | exact GlobalTheory.AbCoh.toHO1_surjective | (intros; apply GlobalTheory.AbCoh.toHO1_surjective <;> assumption)
end
end
