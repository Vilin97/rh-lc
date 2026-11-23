module

public import Development.EtaleCohomology.KummerTheory.InjSlice
public import Development.EtaleCohomology.KummerTheory.OneExPf
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
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
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Linter.Style
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
public import Development.EtaleCohomology.KummerTheory.PrimTorsPf
public import Development.EtaleCohomology.KummerTheory.EtaleKummerDegreeZeroCohomologyOfTwistSectionCla
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.EtaleCohomology.KummerTheory.CupAWCutEv
public import Development.EtaleCohomology.KummerTheory.ShSectPf
public import Development.EtaleCohomology.KummerTheory.StalkPf
public import Development.EtaleCohomology.KummerTheory.SecSHPf

-- Source module: Development.EtaleCohomology.KummerTheory.EtaleNormalizedFreeChainsDifferentialOneZeroEqZe

section

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.KummerTheory.S0

variable (R : Type) [CommRing R] (F : Shv R) (X : Scheme.{0})

def eta (s : Sec F X) : (freeP R).obj (yoneda.obj X) ⟶ F.obj where
  app U := ModuleCat.freeDesc (↾fun (x : ULift.{1} (unop U ⟶ X)) => Sec.res (ULift.down x) s)
  naturality := by
    intro U V g
    apply ModuleCat.free_hom_ext
    intro x
    simp only [freeP, Functor.comp_obj, Functor.whiskeringRight_obj_obj, Functor.comp_map, ModuleCat.hom_comp,
      LinearMap.comp_apply]
    erw [ModuleCat.free_map_apply, ModuleCat.freeDesc_apply, ModuleCat.freeDesc_apply]
    change (F.obj.map (g.unop ≫ x.down).op).hom s = (F.obj.map g).hom ((F.obj.map x.down.op).hom s)
    rw [op_comp, Functor.map_comp]
    rfl

def gmap (s : Sec F X) : (free R).obj (yoneda.obj X) ⟶ F :=
  ⟨sheafifyLift Scheme.etaleTopology (eta R F X s) F.property⟩

theorem gmap_app (s : Sec F X) (U : Scheme.{0}) (x : U ⟶ X) :
    ((gmap R F X s).hom.app (op U)).hom (freeGen R (yoneda.obj X) U x) = Sec.res x s := by
  have h := congrArg (fun f => (f.app (op U)).hom
      (ModuleCat.freeMk (show uliftFunctor.{1, 0}.obj ((yoneda.obj X).obj (op U)) from ULift.up x)))
    (toSheafify_sheafifyLift Scheme.etaleTopology (eta R F X s) F.property)
  exact h.trans (ModuleCat.freeDesc_apply _ _)

theorem etale_normalized_free_chains_differential_one_zero_eq_zero : ((chainsN R).obj (sch.obj X)).d 1 0 = 0 := by
  simp [chainsN, AlgebraicTopology.alternatingFaceMapComplex_obj_d, AlgebraicTopology.AlternatingFaceMapComplex.objD,
    Fin.sum_univ_two, SimplicialObject.δ, sch]
  rfl

theorem d10 : ((chains R).obj (sch.obj X)).d (-1) 0 ≫ (chainsXIso R (sch.obj X) 0).hom = 0 := by
  dsimp only [chainsXIso, chains, Functor.comp_obj]
  erw [HomologicalComplex.extend_d_eq ((chainsN R).obj (sch.obj X)) ComplexShape.embeddingDownNat (i := 1) (j := 0) rfl rfl]
  rw [etale_normalized_free_chains_differential_one_zero_eq_zero]
  simp only [Limits.zero_comp, Limits.comp_zero]
  all_goals rfl

theorem resι_d : resι R F ≫ (res R F).d 0 1 = 0 := by
  rw [resι]
  refine (Category.assoc _ _ _).trans ?_
  erw [(injectiveResolution F).ι'.comm 0 1]
  simp
  all_goals rfl

def fz (s : Sec F X) : ((chains R).obj (sch.obj X)).X (-((0 : ℕ) : ℤ)) ⟶ (res R F).X 0 :=
  (chainsXIso R (sch.obj X) 0).hom ≫ gmap R F X s ≫ resι R F

theorem fz_d (s : Sec F X) : fz R F X s ≫ (res R F).d 0 1 = 0 := by
  have h : (gmap R F X s ≫ resι R F) ≫ (res R F).d 0 1 = 0 := by
    rw [Category.assoc, resι_d, Limits.comp_zero]
  refine (Category.assoc _ _ _).trans ?_
  exact (congrArg (fun t => (chainsXIso R (sch.obj X) 0).hom ≫ t) h).trans Limits.comp_zero

theorem d_fz (s : Sec F X) : ((chains R).obj (sch.obj X)).d (-1) (-((0 : ℕ) : ℤ)) ≫ fz R F X s = 0 := by
  simp only [fz]
  rw [← Category.assoc]
  erw [d10]
  exact Limits.zero_comp

def coc (s : Sec F X) : Cocycle ((chains R).obj (sch.obj X)) (res R F) 0 :=
  Cocycle.mk (Cochain.single (fz R F X s) 0) 1 (zero_add 1) (by
    rw [Cochain.δ_single (fz R F X s) 0 1 (zero_add 1) (-1) 1 (by norm_num) rfl, fz_d, d_fz,
      Cochain.single_zero, Cochain.single_zero, smul_zero, add_zero])

theorem coc_ev (s : Sec F X) (U : Scheme.{0}) (x : U ⟶ X) :
    ev (coc R F X s).1 0 0 (by simp) U x = Sec.res x (Sec.map (resι R F) s) := by
  rw [sec_res_map]
  simp only [ev, coc, Cocycle.mk_coe, Cochain.single_v, fz, Iso.inv_hom_id_assoc]
  change ((resι R F).hom.app (op U)).hom (((gmap R F X s).hom.app (op U)).hom (freeGen R (yoneda.obj X) U x)) = _
  rw [gmap_app]

end LateralTheory.KummerTheory.S0

namespace LateralTheory.KummerTheory

theorem Sec0Ex_of : DegreeZeroSectionExists := fun R _ F X s => ⟨S0.coc R F X s, S0.coc_ev R F X s⟩

end LateralTheory.KummerTheory
end
end
end

-- Source module: Development.EtaleCohomology.KummerTheory.PrimIsPrimitiveRoot

section

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC Polynomial

namespace LateralTheory.KummerTheory

theorem twGen_res {q : ℕ} (i : ℤ) {V U : Scheme.{0}} (f : V ⟶ U) (ζ : Prim q Γ(U, ⊤)) :
    Sec.res f (twGen i ζ) = twGen i (Prim.map f.appTop.hom ζ) := by
  have h := (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)).naturality f.op
  have h2 := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom h)
    (Submodule.Quotient.mk (Finsupp.single ζ 1) : (twF q i).obj Γ(U, ⊤))
  simp only [ModuleCat.hom_comp] at h2
  unfold twGen ofRings.sec
  rw [← Finsupp.mapDomain_single]
  exact h2.symm

theorem twGen_zero_eq {q : ℕ} {V : Scheme.{0}} (ζ ξ : Prim q Γ(V, ⊤)) (a : (ZMod q)ˣ)
    (h : ξ.1 = ζ.1 ^ (a : ZMod q).val) : twGen 0 ξ = twGen 0 ζ := by
  unfold twGen
  congr 1
  refine (Submodule.Quotient.eq _).2 (Submodule.subset_span ⟨ζ, ξ, a, h, ?_⟩)
  simp
  rfl

theorem prim_pow {q : ℕ} {A : Type} [CommRing A] (ζ : Prim q A) : ζ.1 ^ q = 1 := by
  obtain ⟨c, hc⟩ := cyclotomic.dvd_X_pow_sub_one q ℤ
  have h := congrArg (aeval ζ.1) hc
  rw [map_mul, ζ.2.2, zero_mul] at h
  simpa [sub_eq_zero] using h

theorem prim_isPrimitiveRoot {q : ℕ} {K : Type} [Field K] (μ : Prim q K) : IsPrimitiveRoot μ.1 q := by
  obtain ⟨z, hz1, hz2⟩ := μ
  have : NeZero (q : K) := ⟨hz1.ne_zero⟩
  refine (isRoot_cyclotomic_iff).1 ?_
  rw [aeval_def, algebraMap_int_eq] at hz2
  show Polynomial.eval z (cyclotomic q K) = 0
  rw [← map_cyclotomic_int, Polynomial.eval_map]
  exact hz2

theorem local_pow {q : ℕ} [NeZero q] {U : Scheme.{0}} (ζ ξ : Prim q Γ(U, ⊤)) (x : U) :
    ∃ (h : Γ(U, ⊤)) (a : (ZMod q)ˣ), x ∈ U.basicOpen h ∧ h * (ξ.1 - ζ.1 ^ (a : ZMod q).val) = 0 := by
  let e := (U.evaluation ⊤ x trivial).hom
  have hζ := prim_isPrimitiveRoot (Prim.map e ζ)
  have hξ := prim_isPrimitiveRoot (Prim.map e ξ)
  obtain ⟨i, hi, hie⟩ := hζ.eq_pow_of_pow_eq_one hξ.pow_eq_one
  have hcop : i.Coprime q := (hζ.pow_iff_coprime (NeZero.pos q) i).1 (hie ▸ hξ)
  have hav : ((ZMod.unitOfCoprime i hcop : (ZMod q)ˣ) : ZMod q).val = i := by
    simp [ZMod.val_natCast, Nat.mod_eq_of_lt hi]
  obtain ⟨k, hk⟩ := binomExpansion ((X : Polynomial Γ(U, ⊤)) ^ q - 1) ξ.1
    (ζ.1 ^ ((ZMod.unitOfCoprime i hcop : (ZMod q)ˣ) : ZMod q).val - ξ.1)
  have hξq := prim_pow ξ
  have hζq : (ζ.1 ^ ((ZMod.unitOfCoprime i hcop : (ZMod q)ˣ) : ZMod q).val) ^ q = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, prim_pow ζ, one_pow]
  refine ⟨(q : Γ(U, ⊤)) * ξ.1 ^ (q - 1) + k * (ζ.1 ^ ((ZMod.unitOfCoprime i hcop : (ZMod q)ˣ) : ZMod q).val - ξ.1),
    ZMod.unitOfCoprime i hcop, ?_, ?_⟩
  · rw [← Scheme.evaluation_ne_zero_iff_mem_basicOpen (X := U) (U := ⊤) x (show x ∈ (⊤ : U.Opens) from trivial)]
    have hy : e (ζ.1 ^ ((ZMod.unitOfCoprime i hcop : (ZMod q)ˣ) : ZMod q).val - ξ.1) = 0 := by
      rw [map_sub, map_pow, hav, sub_eq_zero]
      exact hie
    have hq : ((q : ℕ) : U.residueField x) ≠ 0 := (Prim.map e ξ).2.1.ne_zero
    change e _ ≠ 0
    rw [map_add (f := _), map_mul, map_mul, hy, mul_zero, add_zero, map_pow, map_natCast]
    exact mul_ne_zero hq (pow_ne_zero _ (hξ.ne_zero (NeZero.ne q)))
  · have hs : ξ.1 + (ζ.1 ^ ((ZMod.unitOfCoprime i hcop : (ZMod q)ˣ) : ZMod q).val - ξ.1) =
        ζ.1 ^ ((ZMod.unitOfCoprime i hcop : (ZMod q)ˣ) : ZMod q).val := by ring
    rw [hs] at hk
    simp only [eval_sub, eval_pow, eval_X, eval_one, hζq, hξq, sub_self, derivative_sub, derivative_X_pow,
      derivative_one, sub_zero, eval_mul, eval_C] at hk
    linear_combination hk

theorem sec_eq_of_cover {R : Type} [CommRing R] {F : Shv R} {U : Scheme.{0}} {ι : Type} (V : ι → U.Opens)
    (hV : TopologicalSpace.IsOpenCover V) (s t : Sec F U) (h : ∀ i, Sec.res (V i).ι s = Sec.res (V i).ι t) :
    s = t := by
  let S : Sieve U := {
    arrows := fun W f => Sec.res f s = Sec.res f t
    downward_closed := by
      intro W W' f hf g
      simp only [Sec.res, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at hf ⊢
      rw [hf] }
  have hS : S ∈ Scheme.etaleTopology U := by
    apply Scheme.zariskiTopology_le_etaleTopology
    refine Scheme.zariskiTopology.superset_covering ?_
      (Scheme.Cover.mem_grothendieckTopology (U.openCoverOfIsOpenCover V hV))
    rw [Sieve.ofArrows, Sieve.generate_le_iff]
    rintro W f ⟨i⟩
    exact h i
  have hsh : Presieve.IsSheaf Scheme.etaleTopology (F.obj ⋙ forget _) :=
    (isSheaf_iff_isSheaf_of_type _ _).1 (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget _) F.property)
  exact (hsh S hS).isSeparatedFor.ext fun W f hf => hf

theorem twGen_zero_indep {q : ℕ} [NeZero q] {U : Scheme.{0}} (ζ ξ : Prim q Γ(U, ⊤)) :
    twGen 0 ξ = twGen 0 ζ := by
  choose h a hx hh using fun x : U => local_pow ζ ξ x
  refine sec_eq_of_cover (fun x => U.basicOpen (h x)) ?_ _ _ fun x => ?_
  · refine eq_top_iff.2 fun y _ => ?_
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨y, hx y⟩
  rw [twGen_res, twGen_res]
  apply twGen_zero_eq _ _ (a x)
  change (U.basicOpen (h x)).ι.appTop.hom ξ.1 = (U.basicOpen (h x)).ι.appTop.hom ζ.1 ^ _
  rw [← map_pow, ← sub_eq_zero, ← map_sub]
  have hu : IsUnit ((U.basicOpen (h x)).ι.appTop.hom (h x)) := by
    rw [Scheme.Opens.ι_appTop]
    have key : ∀ (W : U.Opens) (hW : W = U.basicOpen (h x)) (hle : W ≤ ⊤),
        IsUnit (U.presheaf.map (homOfLE hle).op (h x)) := by
      rintro W rfl hle
      exact RingedSpace.isUnit_res_basicOpen U.toRingedSpace (h x)
    exact key _ (Scheme.Opens.ι_image_top _) _
  exact hu.mul_right_eq_zero.1 (by rw [← map_mul, hh x, map_zero])

theorem TwRes0_of : TwRes0 := by
  intro q _ U X x ζ₀ ζ
  rw [twGen_res]
  exact twGen_zero_indep _ _

end LateralTheory.KummerTheory
end
end
end

-- Source module: Development.EtaleCohomology.KummerTheory.ResNegZero

section

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.KummerTheory.DegreeZeroClassRestriction

theorem res_neg_zero (R : Type) [CommRing R] (F : Shv R) (s : ℤ) (hs : s < 0) : IsZero ((res R F).X s) := by
  apply HomologicalComplex.isZero_extend_X
  intro i hi
  have h' : ((i : ℕ) : ℤ) = s := hi
  omega

def asHom {X U : Scheme.{0}} (x : Sx (sch.obj X) 0 U) : U ⟶ X := by
  unfold sch at x; exact x

def ofHom {X U : Scheme.{0}} (g : U ⟶ X) : Sx (sch.obj X) 0 U := by
  unfold sch; exact g

theorem res_ofHom {X U : Scheme.{0}} (x : Sx (sch.obj X) 0 U) : Sx.res (asHom x) (ofHom (𝟙 X)) = x := by
  change asHom x ≫ 𝟙 X = x
  exact Category.comp_id (asHom x)

theorem cochain_eq (R : Type) [CommRing R] (F : Shv R) (X : Scheme.{0})
    (α β : Cochain ((chains R).obj (sch.obj X)) (res R F) 0)
    (h : ev α 0 0 (by simp) X (𝟙 X) = ev β 0 0 (by simp) X (𝟙 X)) : α = β := by
  apply LateralTheory.KummerTheory.AW.ev_ext
  intro p s hp U x
  cases p with
  | zero =>
    obtain rfl : s = 0 := by simpa using hp.symm
    have key : ∀ γ : Cochain ((chains R).obj (sch.obj X)) (res R F) 0,
        ev γ 0 0 hp U x = Sec.res (asHom x) (ev γ 0 0 hp X (ofHom (𝟙 X))) := by
      intro γ
      rw [LateralTheory.KummerTheory.AW.ev_res]
      rw [res_ofHom]
    rw [key α, key β]
    exact congrArg _ h
  | succ k =>
    have hs : s < 0 := by omega
    rw [LateralTheory.KummerTheory.AW.ev_eq, LateralTheory.KummerTheory.AW.ev_eq, (res_neg_zero R F s hs).eq_of_tgt
      ((chainsXIso R (sch.obj X) (k + 1)).inv ≫ α.v _ _ hp) ((chainsXIso R (sch.obj X) (k + 1)).inv ≫ β.v _ _ hp)]

end LateralTheory.KummerTheory.DegreeZeroClassRestriction

theorem LateralTheory.KummerTheory.Cls0_of (_hT : LateralTheory.KummerTheory.TwSec) : LateralTheory.KummerTheory.Cls0 := by
  intro R _ F X α β h
  have e : α.1 = β.1 := LateralTheory.KummerTheory.DegreeZeroClassRestriction.cochain_eq R F X α.1 β.1 h
  exact congrArg CohomologyClass.mk (Cocycle.ext e)
end
end
end

-- Source module: Development.EtaleCohomology.KummerTheory.FixStalk

section

@[expose] public section

theorem LateralTheory.Fix.Stalk.intersectionNumber_baseChange : LateralTheory.KummerTheory.Stalk := by
  have hT : LateralTheory.KummerTheory.TwSec :=
    LateralTheory.KummerTheory.TwSec_of LateralTheory.KummerTheory.PrimTors_of
      (LateralTheory.KummerTheory.SecSH_of LateralTheory.KummerTheory.ShSectPf.ShSect_of)
  exact LateralTheory.KummerTheory.Stalk_of
    (LateralTheory.KummerTheory.etale_kummer_degree_zero_cohomology_of_twist_section_class_and_root_ex hT (LateralTheory.KummerTheory.Cls0_of hT)
      (LateralTheory.KummerTheory.OneEx_of hT LateralTheory.KummerTheory.TwRes0_of LateralTheory.KummerTheory.Sec0Ex_of))
end
end

-- Source module: Development.EtaleCohomology.KummerTheory.FinStalk

section

@[expose] public section

namespace LateralTheory.Fin.Stalk
theorem etale_cohomology_stalk_compatibility_finite_coefficients_holds : LateralTheory.KummerTheory.Stalk := by
  apply LateralTheory.Fix.Stalk.intersectionNumber_baseChange
theorem intersectionNumber_baseChange : LateralTheory.KummerTheory.Stalk := etale_cohomology_stalk_compatibility_finite_coefficients_holds
end LateralTheory.Fin.Stalk
end
end
