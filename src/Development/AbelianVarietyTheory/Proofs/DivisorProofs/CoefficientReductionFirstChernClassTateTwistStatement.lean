module

public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CorrFamAddTwo
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCochainEvalOnSimplexBasicPropertiesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCochainEvalOnSimplexDifferentialValuesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCochainEvEqOfNaturalStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsImageCocycleSemilinearSheafComplexMapStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernClassTateTwistCocycleUniqueNaturalAddiStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeneralLinearGroupDetMapFinOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefficientReductionFirstChernClassTateTwistAltI
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalPrimitiveRootAndRootsOfUnityStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafSectionsExtAndGlueStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerReductionChernDefectRestrictStatement
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReducedChernCocycleDegOneSubEqDifferential
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerReductionChernDefectSectionRes

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.RedChern

theorem defectSec_res : ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → ∀ (U : Scheme.{0}) (u : (Γ(U, ⊤))ˣ), IsUnit (Q : Γ(U, ⊤)) → ∀ (V : Scheme.{0}) (g : V ⟶ U), Sec.res g (GlobalTheory.EtC.RedChern.defectSec Q q U u) = GlobalTheory.EtC.RedChern.defectSec Q q V (Units.map g.appTop.hom.toMonoidHom u) := by
  intro Q q _ hqQ U u hQ V g
  have hQV : IsUnit (Q : Γ(V, ⊤)) := by
    have := hQ.map g.appTop.hom
    simpa using this
  apply (GlobalTheory.T.etaleSheafSections_ext_and_glue _ _ V).1
  refine loc_mono ((GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity Q V).2.2.2 hQV (Units.map g.appTop.hom.toMonoidHom u)) ?_
  rintro W h ⟨v, hv⟩
  have hres : Sec.res h (Sec.res g (defectSec Q q U u)) = Sec.res (h ≫ g) (defectSec Q q U u) := by
    simp only [Sec.res, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [hres, GlobalTheory.T.kummerReductionChernDefect_restrict Q q hqQ V _ hQV W h v hv]
  refine GlobalTheory.T.kummerReductionChernDefect_restrict Q q hqQ U u hQ W (h ≫ g) v ?_
  rw [hv]
  ext
  simp [Scheme.Hom.comp_appTop] <;> rfl

end GlobalTheory.EtC.RedChern
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerReductionChernDefectSectionResStatement

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.kummerReductionChernDefectSection_res : ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → ∀ (U : Scheme.{0}) (u : (Γ(U, ⊤))ˣ), IsUnit (Q : Γ(U, ⊤)) → ∀ (V : Scheme.{0}) (g : V ⟶ U), Sec.res g (GlobalTheory.EtC.RedChern.defectSec Q q U u) = GlobalTheory.EtC.RedChern.defectSec Q q V (Units.map g.appTop.hom.toMonoidHom u) := by
  first
  | exact @GlobalTheory.EtC.RedChern.defectSec_res
  | exact GlobalTheory.EtC.RedChern.defectSec_res
  | (intros; apply GlobalTheory.EtC.RedChern.defectSec_res <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReducedChernCocycleDegOneSubEqDifferentialStatement

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.reducedChernCocycle_deg_one_sub_eq_differential : ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → ∀ (U : Scheme.{0}) (u : (Γ(U, ⊤))ˣ), IsUnit (Q : Γ(U, ⊤)) → ∀ (a : Sec ((res _ (tw Q 1)).X 1) U) (b : Sec ((res _ (tw q 1)).X 1) U), (∀ (V : Scheme.{0}) (g : V ⟶ U) (v : (Γ(V, ⊤))ˣ), v ^ Q = Units.map g.appTop.hom.toMonoidHom u → Sec.res g a = Sec.map ((res _ (tw Q 1)).d 0 1) (kumT Q V v)) → (∀ (V : Scheme.{0}) (g : V ⟶ U) (w : (Γ(V, ⊤))ˣ), w ^ q = Units.map g.appTop.hom.toMonoidHom u → Sec.res g b = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q V w)) → (redMap Q q 1).app U 1 a - b = Sec.map ((res _ (tw q 1)).d 0 1) (GlobalTheory.EtC.RedChern.defectSec Q q U u) := by
  first
  | exact @GlobalTheory.EtC.RedChern.red_chern_deg_one
  | exact GlobalTheory.EtC.RedChern.red_chern_deg_one
  | (intros; apply GlobalTheory.EtC.RedChern.red_chern_deg_one <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReducedChernCocycleDegTwoSubEqDefects

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem GlobalTheory.RedChern.redMap_cocycle_sub_eq_defects : ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → ∀ (U : Scheme.{0}) (u₁ u₂ : (Γ(U, ⊤))ˣ), IsUnit (Q : Γ(U, ⊤)) → ∀ (a : Sec ((res _ (tw Q 1)).X 0) U) (b : Sec ((res _ (tw q 1)).X 0) U), (∀ (V : Scheme.{0}) (g : V ⟶ U) (v w : (Γ(V, ⊤))ˣ), v ^ Q = Units.map g.appTop.hom.toMonoidHom u₁ → w ^ Q = Units.map g.appTop.hom.toMonoidHom u₂ → Sec.res g a = kumT Q V v + kumT Q V w - kumT Q V (v * w)) → (∀ (V : Scheme.{0}) (g : V ⟶ U) (v w : (Γ(V, ⊤))ˣ), v ^ q = Units.map g.appTop.hom.toMonoidHom u₁ → w ^ q = Units.map g.appTop.hom.toMonoidHom u₂ → Sec.res g b = kumT q V v + kumT q V w - kumT q V (v * w)) → (redMap Q q 1).app U 0 a - b = GlobalTheory.EtC.RedChern.defectSec Q q U u₂ - GlobalTheory.EtC.RedChern.defectSec Q q U (u₁ * u₂) + GlobalTheory.EtC.RedChern.defectSec Q q U u₁ := by
  intro Q q _ hqQ U u₁ u₂ hQ a b ha hb
  refine (GlobalTheory.T.etaleSheafSections_ext_and_glue _ ((res _ (tw q 1)).X 0) U).1 _ _ ?_
  have h1 := (GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity Q U).2.2.2 hQ u₁
  have h2 := (GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity Q U).2.2.2 hQ u₂
  refine GlobalTheory.EtC.RedChern.loc_mono (GlobalTheory.EtC.RedChern.loc_and h1 h2) ?_
  rintro V g ⟨⟨v, hv⟩, ⟨w, hw⟩⟩
  have hvq : (v ^ (Q / q)) ^ q = Units.map g.appTop.hom.toMonoidHom u₁ := by
    rw [← pow_mul, Nat.div_mul_cancel hqQ, hv]
  have hwq : (w ^ (Q / q)) ^ q = Units.map g.appTop.hom.toMonoidHom u₂ := by
    rw [← pow_mul, Nat.div_mul_cancel hqQ, hw]
  have hvw : (v * w) ^ Q = Units.map g.appTop.hom.toMonoidHom (u₁ * u₂) := by
    rw [mul_pow, hv, hw, map_mul]
  have ea := ha V g v w hv hw
  have eb := hb V g _ _ hvq hwq
  have d1 := GlobalTheory.T.kummerReductionChernDefect_restrict Q q hqQ U u₁ hQ V g v hv
  have d2 := GlobalTheory.T.kummerReductionChernDefect_restrict Q q hqQ U u₂ hQ V g w hw
  have d3 := GlobalTheory.T.kummerReductionChernDefect_restrict Q q hqQ U (u₁ * u₂) hQ V g (v * w) hvw
  have en := (redMap Q q 1).nat g 0 a
  have hsub : ∀ x y : Sec ((res _ (tw q 1)).X 0) U, Sec.res g (x - y) = Sec.res g x - Sec.res g y := fun x y => map_sub _ x y
  have hadd : ∀ x y : Sec ((res _ (tw q 1)).X 0) U, Sec.res g (x + y) = Sec.res g x + Sec.res g y := fun x y => map_add _ x y
  rw [hsub, hadd, hsub, en, ea, eb, d1, d2, d3]
  simp only [GlobalTheory.EtC.RedChern.defect, map_sub, map_add (f := _), mul_pow]
  abel
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReducedChernCocycleDegTwoSubEqDefectsStatement

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.reducedChernCocycle_deg_two_sub_eq_defects : ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → ∀ (U : Scheme.{0}) (u₁ u₂ : (Γ(U, ⊤))ˣ), IsUnit (Q : Γ(U, ⊤)) → ∀ (a : Sec ((res _ (tw Q 1)).X 0) U) (b : Sec ((res _ (tw q 1)).X 0) U), (∀ (V : Scheme.{0}) (g : V ⟶ U) (v w : (Γ(V, ⊤))ˣ), v ^ Q = Units.map g.appTop.hom.toMonoidHom u₁ → w ^ Q = Units.map g.appTop.hom.toMonoidHom u₂ → Sec.res g a = kumT Q V v + kumT Q V w - kumT Q V (v * w)) → (∀ (V : Scheme.{0}) (g : V ⟶ U) (v w : (Γ(V, ⊤))ˣ), v ^ q = Units.map g.appTop.hom.toMonoidHom u₁ → w ^ q = Units.map g.appTop.hom.toMonoidHom u₂ → Sec.res g b = kumT q V v + kumT q V w - kumT q V (v * w)) → (redMap Q q 1).app U 0 a - b = GlobalTheory.EtC.RedChern.defectSec Q q U u₂ - GlobalTheory.EtC.RedChern.defectSec Q q U (u₁ * u₂) + GlobalTheory.EtC.RedChern.defectSec Q q U u₁ := by
  first
  | exact @GlobalTheory.RedChern.redMap_cocycle_sub_eq_defects
  | exact GlobalTheory.RedChern.redMap_cocycle_sub_eq_defects
  | (intros; apply GlobalTheory.RedChern.redMap_cocycle_sub_eq_defects <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefficientReductionFirstChernClassTateTwist

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.RedChern

set_option backward.isDefEq.respectTransparency false

theorem delta_two_eq : (SimplexCategory.δ (2 : Fin 3) : SimplexCategory.mk 1 ⟶ SimplexCategory.mk 2) =
    SimplexCategory.subinterval 0 1 (by omega) := by
  ext i; fin_cases i <;> rfl

theorem delta_zero_eq : (SimplexCategory.δ (0 : Fin 3) : SimplexCategory.mk 1 ⟶ SimplexCategory.mk 2) =
    SimplexCategory.subinterval 1 1 (by omega) := by
  ext i; fin_cases i <;> rfl

theorem face_two {E : Spc} {U : Scheme.{0}} (x : Sx E 2 U) : x.face 2 = x.sub 0 1 (by omega) := by
  unfold Sx.face Sx.sub SimplicialObject.δ
  rw [delta_two_eq]

theorem face_zero {E : Spc} {U : Scheme.{0}} (x : Sx E 2 U) : x.face 0 = x.sub 1 1 (by omega) := by
  unfold Sx.face Sx.sub SimplicialObject.δ
  rw [delta_zero_eq]

theorem sub_res {E : Spc} {N : ℕ} {V U : Scheme.{0}} (g : V ⟶ U) (x : Sx E N U) (j l : ℕ) (h : j + l ≤ N) :
    (x.res g).sub j l h = (x.sub j l h).res g := by
  unfold Sx.sub Sx.res
  exact NatTrans.naturality_apply (E.map (SimplexCategory.subinterval j l h).op) g.op x

open GlobalTheory.EtC.PicSpec

theorem corrFam_nat (Q q : ℕ) [NeZero Q] (hqQ : q ∣ Q) {E : Spc} (hE : Inv Q E) (L : E ⟶ ofCat (glCat 1)) (p : ℕ) (s : ℤ)
    (h : -(p : ℤ) + 1 = s) (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U) :
    Sec.res g (corrFam Q q L p s h U x) = corrFam Q q L p s h V (x.res g) := by
  match p with
  | 0 =>
    rw [corrFam_zero, corrFam_zero]
    exact map_zero (((res _ (tw q 1)).X s).obj.map g.op).hom
  | 1 =>
    obtain rfl : s = 0 := by omega
    rw [corrFam_one, corrFam_one, lineUnit_res,
      GlobalTheory.T.kummerReductionChernDefectSection_res Q q hqQ U _ (hE U ⟨x.face 0⟩) V g]
  | p + 2 =>
    rw [corrFam_add_two, corrFam_add_two]
    exact map_zero (((res _ (tw q 1)).X s).obj.map g.op).hom

theorem coefficientReduction_firstChernClass_tateTwist : ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → ∀ E : Spc, Inv Q E → ∀ L : E ⟶ ofCat (glCat 1),
    red Q q E 2 1 (c1 Q L) = c1 q L := by
  intro Q q _ hqQ E hE L
  have hq0 : q ≠ 0 := by
    rintro rfl
    exact NeZero.ne Q (Nat.eq_zero_of_zero_dvd hqQ)
  haveI : NeZero q := ⟨hq0⟩
  have hUnit : Inv q E := fun U hU => by
    obtain ⟨k, hk⟩ := hqQ
    have := hE U hU
    rw [hk, Nat.cast_mul] at this
    exact isUnit_of_mul_isUnit_left this
  obtain ⟨γ, hγ, hγ0, hγ1, hγ2⟩ := (GlobalTheory.T.firstChernClassTateTwist_cocycle_unique_natural_additive Q).1 L hE
  obtain ⟨γ', hγ', hγ0', hγ1', hγ2'⟩ := (GlobalTheory.T.firstChernClassTateTwist_cocycle_unique_natural_additive q).1 L hUnit
  obtain ⟨β, hβ⟩ := (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap _ _ (redMap Q q 1)).1 E 2 γ
  have hred : red Q q E 2 1 (c1 Q L) = CohomologyClass.mk β := by
    rw [← hγ]
    exact (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap _ _ (redMap Q q 1)).2 E 2 γ β hβ
  rw [hred, ← hγ']
  obtain ⟨α, hα⟩ := GlobalTheory.T.exists_cochain_ev_eq_of_natural' (ZMod q) (corrFam Q q L) (corrFam_nat Q q hqQ hE L)
  rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ 1 (by norm_num)]
  refine ⟨α, ?_⟩
  apply (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.2.1
  intro p t ht U x
  rw [Cocycle.coe_sub, ((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).1 _ _ p t ht U x).2.1, hβ]
  match p with
  | 0 =>
    obtain rfl : t = 2 := by omega
    rw [(GlobalTheory.T.etaleCochainEvalOnSimplex_differential_values (ZMod q) (by norm_num) α U).1 x, hα, corrFam_zero, sec_map_zero, hγ0, hγ0', map_zero, sub_zero]
  | 1 =>
    obtain rfl : t = 1 := by omega
    have key := (GlobalTheory.T.etaleCochainEvalOnSimplex_differential_values (ZMod q) (by norm_num) α U).2 0 0 1 (by simp) ht x
    rw [key]
    simp only [hα, corrFam_zero, smul_zero, Finset.sum_const_zero, add_zero, corrFam_one]
    refine (GlobalTheory.T.reducedChernCocycle_deg_one_sub_eq_differential Q q hqQ U (lineUnit L x) (hE U ⟨x.face 0⟩) _ _ (fun V g v hv => ?_) (fun V g w hw => ?_)).symm
    · rw [(GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod Q)).2.1 γ.1 1 1 _ V U g x]
      exact hγ1 V (x.res g) v (by simpa only [lineUnit_res] using hv)
    · rw [(GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.1 γ'.1 1 1 _ V U g x]
      exact hγ1' V (x.res g) w (by simpa only [lineUnit_res] using hw)
  | 2 =>
    obtain rfl : t = 0 := by omega
    have key := (GlobalTheory.T.etaleCochainEvalOnSimplex_differential_values (ZMod q) (by norm_num) α U).2 1 (-1) 0 (by simp) ht x
    rw [key]
    simp only [hα, corrFam_one]
    rw [show corrFam Q q L (1 + 1) (-1) (by simp) U x = 0 from rfl, sec_map_zero, zero_add, Fin.sum_univ_three,
      lineUnit_face, face_zero, face_two]
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one, one_smul, neg_smul, Int.reduceNeg]
    rw [Int.negOnePow_even 2 (by decide), one_smul, mul_comm (lineUnit L _) (lineUnit L _), ← sub_eq_add_neg]
    norm_num
    refine (GlobalTheory.T.reducedChernCocycle_deg_two_sub_eq_defects Q q hqQ U _ _ (hE U ⟨(x.face 0).face 0⟩) _ _ (fun V g v w hv hw => ?_) (fun V g v w hv hw => ?_)).symm
    · rw [(GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod Q)).2.1 γ.1 2 0 _ V U g x]
      exact hγ2 V (x.res g) v w (by rw [sub_res, lineUnit_res]; exact hv) (by rw [sub_res, lineUnit_res]; exact hw)
    · rw [(GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.1 γ'.1 2 0 _ V U g x]
      exact hγ2' V (x.res g) v w (by rw [sub_res, lineUnit_res]; exact hv) (by rw [sub_res, lineUnit_res]; exact hw)
  | p + 3 =>
    have hZ := res_isZero (tw q 1) t (by omega)
    exact (sec_eq_zero hZ _).trans (sec_eq_zero hZ _).symm

end GlobalTheory.EtC.RedChern
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefficientReductionFirstChernClassTateTwistStatement

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.red_c1_eq_c1_of_dvd : ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → ∀ E : Spc, Inv Q E → ∀ L : E ⟶ ofCat (glCat 1), red Q q E 2 1 (c1 Q L) = c1 q L := by
  first
  | exact @GlobalTheory.EtC.RedChern.coefficientReduction_firstChernClass_tateTwist
  | exact GlobalTheory.EtC.RedChern.coefficientReduction_firstChernClass_tateTwist
  | (intros; apply GlobalTheory.EtC.RedChern.coefficientReduction_firstChernClass_tateTwist <;> assumption)
end
end
