module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsE8WeightedBundle
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsArBaseAway
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSharpBasisSharpBasis
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
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBase
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymplecticBasisE8FactorTorsionStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.E8ActionProductEqOne
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.WeilIsOfLbIsoCubeLB
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.WeilIsGrpPullbackIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SymplecticTorsionSystemIsGeometricBasis
import Mathlib.Tactic.Basify

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.E8ProductTorsionSectionBound

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.Poinc.Sep.E8Fibration.Lab

def postHom {S : Scheme.{0}} (T : Over S) {A B : Over S} [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f] :
    (T ⟶ A) →* (T ⟶ B) where
  toFun x := x ≫ f
  map_one' := by simp
  map_mul' x y := by simp [MonObj.mul_comp]

def preHom {S : Scheme.{0}} {T A : Over S} (x : T ⟶ A) (B : Over S) [GrpObj B] :
    (A ⟶ B) →* (T ⟶ B) where
  toFun y := x ≫ y
  map_one' := by simp
  map_mul' y z := by simp [MonObj.comp_mul]

theorem zpow_finset_sum {G J : Type} [CommGroup G] (g : G) (s : Finset J) (e : J → ℤ) :
    g ^ (∑ i ∈ s, e i) = ∏ i ∈ s, g ^ e i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, zpow_add, ih]

theorem prod_prod_zpow {G C J : Type} [CommGroup G] [Fintype C] [Fintype J] (b : C → G) (x : J → C → ℤ) (k : J → ℤ) :
    ∏ i, (∏ c, b c ^ x i c) ^ k i = ∏ c, b c ^ (∑ i, k i * x i c) := by
  simp only [← Finset.prod_zpow, ← zpow_mul, zpow_finset_sum]
  rw [Finset.prod_comm]
  simp only [mul_comm]

theorem pow_val_intCast {G : Type} [Group G] {N : ℕ} (hN : 0 < N) {g : G} (hg : g ^ N = 1) (k : ℤ) :
    g ^ ((k : ZMod N)).val = g ^ k := by
  haveI : NeZero N := ⟨hN.ne'⟩
  rw [← zpow_natCast, ZMod.val_intCast]
  exact (zpow_eq_zpow_emod' k hg).symm

theorem prod_zpow_pow_eq_one {G C : Type} [CommGroup G] [Fintype C] {N : ℕ} {b : C → G} (hb : ∀ c, b c ^ N = 1)
    (x : C → ℤ) : (∏ c, b c ^ x c) ^ N = 1 := by
  rw [← Finset.prod_pow]
  refine Finset.prod_eq_one fun c _ => ?_
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hb, one_zpow]

theorem sum_labMat_mul (W : Matrix (Fin 8) (Fin 8) ℤ) (hW : (e8 W).det = 1) (h : ℕ) (a : Fin 2)
    (i : Fin (2 * (8 * h))) (u : Fin 8) (c : Fin h ⊕ Fin h) :
    ∑ i', labMat W hW h a i' i * sharpBasis W hW h (Pi.single i' 1) u c =
      ∑ v, actMat W a u v * sharpBasis W hW h (Pi.single i 1) v c := by
  have key : ∀ y : Fin (2 * (8 * h)) → ℤ,
      ∑ i', y i' * sharpBasis W hW h (Pi.single i' 1) u c = sharpBasis W hW h y u c := by
    intro y
    conv_rhs => rw [pi_eq_sum_univ' y]

    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact (key _).trans (congrFun (congrFun ((sharpBasis W hW h).apply_symm_apply _) u) c)

theorem ptOf_torsion_and_act : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ) (hW : IsE8 W) (gQ : ℕ) {S : Scheme.{0}} (A B : Over S) [GrpObj A] [IsCommMonObj A]
  [GrpObj B] [IsCommMonObj B] (pr : Fin 8 → (A ⟶ B)) (hP : E8Fibration.IsProd pr) (N : ℕ) {T : Over S}
  (b : Fin gQ ⊕ Fin gQ → (T ⟶ B)), (∀ c, b c ^ N = 1) → 0 < N →
  (∀ i, E8Fibration.Lab.ptOf hP b (E8Fibration.Lab.sharpBasis W hW.2 gQ (Pi.single i 1)) ^ N = 1) ∧
  ∀ (act : Fin 2 → (A ⟶ A)), (∀ i, E8Fibration.ActsBy pr (act i) (E8Fibration.actMat W i)) → ∀ (a : Fin 2) (i : Fin (2 * (8 * gQ))),
    E8Fibration.Lab.ptOf hP b (E8Fibration.Lab.sharpBasis W hW.2 gQ (Pi.single i 1)) ≫ act a =
      Out.linComb (fun i' => E8Fibration.Lab.ptOf hP b (E8Fibration.Lab.sharpBasis W hW.2 gQ (Pi.single i' 1)))
        (fun i' => ((E8Fibration.Lab.labMat W hW.2 gQ a i' i : ZMod N)).val) := by
  intro W hW gQ S A B _ _ _ _ pr hP N T b hb hN
  have ext : ∀ x y : T ⟶ A, (∀ u, x ≫ pr u = y ≫ pr u) → x = y := fun x y h =>
    (hP.2 T fun u => y ≫ pr u).unique h fun _ => rfl
  refine ⟨fun i => ext _ _ fun u => ?_, fun act hact a i => ext _ _ fun u => ?_⟩
  · haveI := hP.1 u
    have := map_pow (postHom T (pr u)) (ptOf hP b (sharpBasis W hW.2 gQ (Pi.single i 1))) N
    refine this.trans ?_
    change (ptOf hP b _ ≫ pr u) ^ N = _
    rw [ptOf_pr, prod_zpow_pow_eq_one hb]
    exact (map_one (postHom T (pr u))).symm
  · haveI := hP.1 u
    have h1 : (ptOf hP b (sharpBasis W hW.2 gQ (Pi.single i 1)) ≫ act a) ≫ pr u =
        ∏ c, b c ^ (∑ v, actMat W a u v * sharpBasis W hW.2 gQ (Pi.single i 1) v c) := by
      rw [Category.assoc, hact a u, ← prod_prod_zpow]
      refine (map_prod (preHom (ptOf hP b (sharpBasis W hW.2 gQ (Pi.single i 1))) B) _ _).trans ?_
      refine Finset.prod_congr rfl fun v _ => ?_
      rw [map_zpow, ← ptOf_pr hP]
      rfl
    rw [h1, Out.linComb, List.prod_ofFn]
    refine Eq.trans ?_ (map_prod (postHom T (pr u)) _ _).symm
    simp only [← sum_labMat_mul W hW.2 gQ a i u]
    rw [← prod_prod_zpow]
    refine Finset.prod_congr rfl fun i' _ => ?_
    rw [map_pow, ← pow_val_intCast hN (prod_zpow_pow_eq_one hb _), ← ptOf_pr hP]
    rfl

end GlobalTheory.Poinc.Sep.E8Fibration.Lab
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.E8ProductTorsionSectionBoundStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.e8_prod_torsion_section_bound : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ) (hW : IsE8 W) (gQ : ℕ) {S : Scheme.{0}} (A B : Over S) [GrpObj A] [IsCommMonObj A]
  [GrpObj B] [IsCommMonObj B] (pr : Fin 8 → (A ⟶ B)) (hP : E8Fibration.IsProd pr) (N : ℕ) {T : Over S}
  (b : Fin gQ ⊕ Fin gQ → (T ⟶ B)), (∀ c, b c ^ N = 1) → ∀ (_hN : 0 < N := by assumption),
  (∀ i, E8Fibration.Lab.ptOf hP b (E8Fibration.Lab.sharpBasis W hW.2 gQ (Pi.single i 1)) ^ N = 1) ∧
  ∀ (act : Fin 2 → (A ⟶ A)), (∀ i, E8Fibration.ActsBy pr (act i) (E8Fibration.actMat W i)) → ∀ (a : Fin 2) (i : Fin (2 * (8 * gQ))),
    E8Fibration.Lab.ptOf hP b (E8Fibration.Lab.sharpBasis W hW.2 gQ (Pi.single i 1)) ≫ act a =
      Out.linComb (fun i' => E8Fibration.Lab.ptOf hP b (E8Fibration.Lab.sharpBasis W hW.2 gQ (Pi.single i' 1)))
        (fun i' => ((E8Fibration.Lab.labMat W hW.2 gQ a i' i : ZMod N)).val) := by
  first | exact @GlobalTheory.Poinc.Sep.E8Fibration.Lab.ptOf_torsion_and_act | exact GlobalTheory.Poinc.Sep.E8Fibration.Lab.ptOf_torsion_and_act | (intros; apply GlobalTheory.Poinc.Sep.E8Fibration.Lab.ptOf_torsion_and_act <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingE8PowerDependsOnForm

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Poinc.Sep.E8Fibration.PairVal

open GlobalTheory.PairingOfLam GlobalTheory.DescentPairing GlobalTheory.AdjointOfPairing

variable {S : Scheme.{0}}

theorem weilIs_of_lbIso {A B : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B]
    (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hB : IsAbelianScheme B) {N : RigLB A}
    (cN : CubicalStr A N) (f g f' g' : B ⟶ A) [IsMonHom f] [IsMonHom g] [IsMonHom f'] [IsMonHom g']
    (H : LBIso (cubeLB A ![fst B B ≫ f, snd B B ≫ g] N.L) (cubeLB A ![fst B B ≫ f', snd B B ≫ g'] N.L))
    {T : Over S} (p₀ : T.left) (hT : ∀ p : T.left, p = p₀) (n : ℕ) (y z : T ⟶ B) (hy : y ^ n = 1) (hz : z ^ n = 1)
    (e : Γ(T.left, ⊤)ˣ) (he : WeilIs A N.L n (y ≫ f') (z ≫ g') e) : WeilIs A N.L n (y ≫ f) (z ≫ g) e := by
  have hyf : (y ≫ f) ^ n = 1 := by rw [← MonObj.pow_comp, hy, MonObj.one_comp]
  have hyc : (y ≫ f') ^ n = 1 := by rw [← MonObj.pow_comp, hy, MonObj.one_comp]
  have hzg : (z ≫ g) ^ n = 1 := by rw [← MonObj.pow_comp, hz, MonObj.one_comp]
  obtain ⟨e', hr⟩ := WeilCube.exists_isRatio cN n _ _ hyf hzg
  have he' := (WeilCube.weilIs_iff cN hG hA hyf hzg hr e').2 rfl
  refine (WeilCube.weilIs_iff cN hG hA hyf hzg hr e).2 (unit_ext fun p _ => ?_)
  obtain ⟨t, ht, v⟩ := exists_gen_lam hG hA cN p₀ hT f' g' n y hyc
  obtain ⟨t', ht', v'⟩ := exists_gen_lam hG hA cN p₀ hT f g n y hyf
  choose J hJ using fun χ : T.left ⟶ A.left => exists_chart N.isLB (χ p)
  have r := val_ratio N.isLB N.isLB H _ t ht t' ht' (fst T B).left (WeilCube.surj_fst hG hB T)
    (lift (𝟙 T) z).left (lift (𝟙 T) (1 : T ⟶ B)).left
    (by rw [← Over.comp_left, ← Over.comp_left, comp_lift, comp_lift, lift_fst_assoc, lift_fst_assoc,
      MonObj.comp_pow, MonObj.comp_pow, lift_snd, lift_snd, hz, one_pow])
    (by rw [← Over.comp_left, ← Over.comp_left, lift_fst, lift_fst]) p hJ hJ
  rw [v z e hz he p J hJ, v' z e' hz he' p J hJ] at r
  apply Additive.ofMul.injective
  have r' := congrArg Additive.ofMul r
  simp only [ofMul_mul, ofMul_inv] at r'
  linear_combination (norm := abel) r'

theorem exists_hom {A B : Over S} [GrpObj A] [GrpObj B] [IsCommMonObj B] {pr : Fin 8 → (A ⟶ B)} (hP : IsProd pr)
    (s : Fin 8 → ℤ) : ∃ f : B ⟶ A, IsMonHom f ∧ ∀ (T : Over S) (x : T ⟶ B) (a : Fin 8), (x ≫ f) ≫ pr a = x ^ s a := by
  obtain ⟨f, hf, -⟩ := hP.2 B (fun a => 𝟙 B ^ s a)
  have h : ∀ (T : Over S) (x : T ⟶ B) (a : Fin 8), (x ≫ f) ≫ pr a = x ^ s a := fun T x a => by
    rw [Category.assoc, hf a]
    exact (map_zpow (PrimPic.preH (G := B) x) _ _).trans (congrArg (· ^ s a) (Category.comp_id x))
  refine ⟨f, isMonHom_of_mul f fun T x y => ?_, h⟩
  refine (hP.2 T fun a => ((x * y) ≫ f) ≫ pr a).unique (fun a => rfl) fun a => ?_
  haveI := hP.1 a
  rw [MonObj.mul_comp, h, h, h, mul_zpow]

theorem bil_zpow {B : Over S} [GrpObj B] [IsCommMonObj B] (M : RigLB B) (cub : CubicalStr B M) {T : Over S}
    (m : Matrix (Fin 8) (Fin 8) ℤ) (s t : Fin 8 → ℤ) (x y : T ⟶ B) :
    PrimPic.bil (GlobalTheory.CechPic.cls M.L M.isLB) m (fun a => x ^ s a) (fun b => y ^ t b) =
      dotProduct s (m.mulVec t) • PrimPic.lam (GlobalTheory.CechPic.cls M.L M.isLB) x y := by
  have hl : ∀ (k : ℤ) (u v : T ⟶ B), PrimPic.lam (GlobalTheory.CechPic.cls M.L M.isLB) (u ^ k) v =
      k • PrimPic.lam (GlobalTheory.CechPic.cls M.L M.isLB) u v := fun k u v =>
    map_zsmul (PrimPic.lamHom M cub v) k (Additive.ofMul u)
  have hr : ∀ (k : ℤ) (u v : T ⟶ B), PrimPic.lam (GlobalTheory.CechPic.cls M.L M.isLB) u (v ^ k) =
      k • PrimPic.lam (GlobalTheory.CechPic.cls M.L M.isLB) u v := fun k u v => by
    rw [PrimPic.lam_comm, hl, PrimPic.lam_comm]
  simp only [PrimPic.bil, hl, hr, dotProduct, Matrix.mulVec, Finset.mul_sum, Finset.sum_smul, smul_smul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  congr 1
  ring

theorem weilIs_of_form_eq : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (gQ : ℕ) (K : Type) [Field K] [IsAlgClosed K] (P' : PolAV (Sp K))
  (B : Over (Sp K)) [GrpObj B] [IsCommMonObj B] (M : RigLB B) (pr : Fin 8 → (P'.A ⟶ B)),
  E8Fibration.IsPPFib B gQ M → E8Fibration.IsProd pr → E8Fibration.IsE8WeightedBundle W pr P'.L M.L → ∀ (N : ℕ), 0 < N → ∀ (s t s' t' : Fin 8 → ℤ),
  dotProduct s ((E8Fibration.e8 W).mulVec t) = dotProduct s' ((E8Fibration.e8 W).mulVec t') →
  ∀ (p q : Out.baseOver (Sp K) ⟶ B), p ^ N = 1 → q ^ N = 1 →
  ∀ (x y x' y' : Out.baseOver (Sp K) ⟶ P'.A), (∀ u, x ≫ pr u = p ^ s u) → (∀ u, y ≫ pr u = q ^ t u) →
    (∀ u, x' ≫ pr u = p ^ s' u) → (∀ u, y' ≫ pr u = q ^ t' u) →
    ∀ c, Out.WeilIs P'.A P'.L N x y c → Out.WeilIs P'.A P'.L N x' y' c := by
  intro W _ gQ K _ _ P' B _ _ M pr hF hP hE N _ s t s' t' hst p q hp hq x y x' y' hx hy hx' hy' c hc
  letI := P'.isAb.comm
  obtain ⟨cub⟩ := hF.2.2.1
  obtain ⟨r, hr, ⟨cL⟩⟩ := GlobalTheory.PolAV_exists_cubical GlobalTheory.abelianSchemeLaws_all.1.cube P'
  obtain ⟨f, hfm, hf⟩ := exists_hom hP s
  obtain ⟨g, hgm, hg⟩ := exists_hom hP t
  obtain ⟨f', hfm', hf'⟩ := exists_hom hP s'
  obtain ⟨g', hgm', hg'⟩ := exists_hom hP t'
  have ex : x = p ≫ f := (hP.2 _ fun u => p ^ s u).unique hx (hf _ p)
  have ey : y = q ≫ g := (hP.2 _ fun u => q ^ t u).unique hy (hg _ q)
  have ex' : x' = p ≫ f' := (hP.2 _ fun u => p ^ s' u).unique hx' (hf' _ p)
  have ey' : y' = q ≫ g' := (hP.2 _ fun u => q ^ t' u).unique hy' (hg' _ q)
  subst ex ey ex' ey'
  have hc₁ : (cubeLB P'.A ![fst B B ≫ f', snd B B ≫ g'] P'.L).IsLB := LB.isLB_linComb P'.isLB _ _
  have hc₂ : (cubeLB P'.A ![fst B B ≫ f, snd B B ≫ g] P'.L).IsLB := LB.isLB_linComb P'.isLB _ _
  have H : LBIso (cubeLB P'.A ![fst B B ≫ f', snd B B ≫ g'] P'.L) (cubeLB P'.A ![fst B B ≫ f, snd B B ≫ g] P'.L) := by
    refine (GlobalTheory.CechPic.cls_eq_iff hc₁ hc₂).1 ?_
    rw [PrimPic.cube_class_e8Bundle_eighth_power W pr hP.1 P'.L P'.isLB M cub hE, PrimPic.cube_class_e8Bundle_eighth_power W pr hP.1 P'.L P'.isLB M cub hE,
      funext (hf _ (fst B B)), funext (hg _ (snd B B)), funext (hf' _ (fst B B)), funext (hg' _ (snd B B)),
      bil_zpow M cub, bil_zpow M cub, hst]
  have : Subsingleton (Out.baseOver (Sp K)).left := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  exact weilIs_of_lbIso GlobalTheory.abelianSchemeLaws_all.1.globalFns P'.isAb hF.1 cL f' g' f g H
    (T := Out.baseOver (Sp K)) (default : PrimeSpectrum K) (fun _ => Subsingleton.elim _ _) N p q hp hq c hc

end GlobalTheory.Poinc.Sep.E8Fibration.PairVal

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingE8PowerDependsOnFormStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.weilPairing_e8Power_depends_on_form : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (gQ : ℕ) (K : Type) [Field K] [IsAlgClosed K] (P' : PolAV (Sp K))
  (B : Over (Sp K)) [GrpObj B] [IsCommMonObj B] (M : RigLB B) (pr : Fin 8 → (P'.A ⟶ B)),
  E8Fibration.IsPPFib B gQ M → E8Fibration.IsProd pr → E8Fibration.IsE8WeightedBundle W pr P'.L M.L → ∀ (N : ℕ), 0 < N → ∀ (s t s' t' : Fin 8 → ℤ),
  dotProduct s ((E8Fibration.e8 W).mulVec t) = dotProduct s' ((E8Fibration.e8 W).mulVec t') →
  ∀ (p q : Out.baseOver (Sp K) ⟶ B), p ^ N = 1 → q ^ N = 1 →
  ∀ (x y x' y' : Out.baseOver (Sp K) ⟶ P'.A), (∀ u, x ≫ pr u = p ^ s u) → (∀ u, y ≫ pr u = q ^ t u) →
    (∀ u, x' ≫ pr u = p ^ s' u) → (∀ u, y' ≫ pr u = q ^ t' u) →
    ∀ c, Out.WeilIs P'.A P'.L N x y c → Out.WeilIs P'.A P'.L N x' y' c := by
  first | exact @GlobalTheory.Poinc.Sep.E8Fibration.PairVal.weilIs_of_form_eq | exact GlobalTheory.Poinc.Sep.E8Fibration.PairVal.weilIs_of_form_eq | (intros; apply GlobalTheory.Poinc.Sep.E8Fibration.PairVal.weilIs_of_form_eq <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.E8FibrationAlgebraicallyClosedField

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.Poinc.Sep.E8Fibration.Lab

theorem exists_symplectic_labels : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (gQ : ℕ),
  ∃ Mat : Fin 2 → Matrix (Fin (2 * (8 * gQ))) (Fin (2 * (8 * gQ))) ℤ,
  ∀ (l : ℕ), l.Prime → Odd l → ∀ j : ℕ, 1 ≤ j →
  ∀ (K : Type) [Field K] [IsAlgClosed K] (k₀ : Subfield K), IsAlgClosed k₀ → (l : K) ≠ 0 →
  ∀ (P' : PolAV (Sp K)), P'.g = 8 * gQ →
  ∀ (B : Over (Sp K)) [GrpObj B] [IsCommMonObj B] (M : RigLB B) (pr : Fin 8 → (P'.A ⟶ B)),
  E8Fibration.IsPPFib B gQ M → E8Fibration.IsProd pr → E8Fibration.IsE8WeightedBundle W pr P'.L M.L →
  ∀ act : Fin 2 → (P'.A ⟶ P'.A), (∀ i, IsMonHom (act i)) → (∀ i, E8Fibration.ActsBy pr (act i) (E8Fibration.actMat W i)) →
  ∃ (bT : TBase k₀ ((l ^ j) ^ 2)) (pt : Fin (2 * (8 * gQ)) → (Out.baseOver (Sp K) ⟶ P'.A)),
    (∀ i, pt i ^ ((l ^ j) ^ 2) = 1) ∧
    (∀ (K' : Type) [Field K'] [IsAlgClosed K'] (x : Sp K' ⟶ Sp K) (y : Over.mk x ⟶ P'.A), y ^ ((l ^ j) ^ 2) = 1 →
      ∃! c : Ix (8 * gQ) ((l ^ j) ^ 2), Out.linComb (fun i => (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver (Sp K)) ≫ pt i)
        (fun i => (c i).val) = y) ∧
    (∀ i i', Out.WeilIs P'.A P'.L (((l ^ j) ^ 2 : ℕ) : ℤ) (pt i) (pt i')
      (unitS (spMap k₀.subtype) bT.ζ ^ Out.stdSymp (8 * gQ) i i')) ∧
    ∀ (a : Fin 2) i, pt i ≫ act a = Out.linComb pt (fun i' => ((Mat a i' i : ZMod ((l ^ j) ^ 2))).val) := by
  intro W hW gQ
  refine ⟨E8Fibration.Lab.labMat W hW.2 gQ, ?_⟩
  intro l hl hlo j hj K _ _ k₀ hk₀ hlK P' hg B _ _ M pr hPP hP hE act hact hacts
  obtain ⟨L1, -⟩ := GlobalTheory.abelianSchemeLaws_all
  have hNK : (((l ^ j) ^ 2 : ℕ) : K) ≠ 0 := by push_cast; exact pow_ne_zero _ (pow_ne_zero _ hlK)
  have hNodd : Odd ((l ^ j) ^ 2) := (hlo.pow).pow
  have hNpos : 0 < (l ^ j) ^ 2 := hNodd.pos
  have hN0 : (((l ^ j) ^ 2 : ℕ) : k₀) ≠ 0 := fun h => hNK (by simpa using congrArg k₀.subtype h)
  haveI : NeZero (((l ^ j) ^ 2 : ℕ) : k₀) := ⟨hN0⟩
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic ((l ^ j) ^ 2) k₀)
    (Polynomial.degree_cyclotomic_pos _ k₀ hNpos).ne'
  have hp : IsPrimitiveRoot ζ ((l ^ j) ^ 2) := (Polynomial.isRoot_cyclotomic_iff).1 hζ
  let bT : TBase k₀ ((l ^ j) ^ 2) := ⟨(hp.isUnit hNpos.ne').unit, hN0.isUnit, fun K' _ β => hp.map_of_injective β.injective⟩
  let z : Kˣ := Units.map k₀.subtype.toMonoidHom bT.ζ
  have hz : IsPrimitiveRoot z ((l ^ j) ^ 2) := IsPrimitiveRoot.coe_units_iff.1 (bT.prim K k₀.subtype)
  have hu : unitS (spMap k₀.subtype) bT.ζ = unitOn z := by
    ext
    simp only [unitS, unitOn, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, z]
    have := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom k₀.subtype)
    exact (congrArg (fun f => f.hom (bT.ζ : k₀)) this).symm
  obtain ⟨b, hb, hpair⟩ := GlobalTheory.T.exists_symplecticBasis_e8Factor_torsion W hW gQ _ hNodd K hNK z hz P' hg B pr hP
    (GlobalTheory.T.weilPairing_e8Power_depends_on_form W hW gQ K P' B M pr hPP hP hE _ hNpos)
  have := P'.isAb.comm
  obtain ⟨htor, hactc⟩ := GlobalTheory.T.e8_prod_torsion_section_bound W hW gQ P'.A B pr hP ((l ^ j) ^ 2) b hb
  have hpt : ∀ i i', Out.WeilIs P'.A P'.L ((l ^ j) ^ 2 : ℕ)
      (E8Fibration.Lab.ptOf hP b (E8Fibration.Lab.sharpBasis W hW.2 gQ (Pi.single i 1)))
      (E8Fibration.Lab.ptOf hP b (E8Fibration.Lab.sharpBasis W hW.2 gQ (Pi.single i' 1))) (unitOn z ^ Out.stdSymp (8 * gQ) i i') := by
    intro i i'
    have h1 := hpair (E8Fibration.Lab.sharpBasis W hW.2 gQ (Pi.single i 1)) (E8Fibration.Lab.sharpBasis W hW.2 gQ (Pi.single i' 1))
      _ _ (E8Fibration.Lab.ptOf_pr hP b _) (E8Fibration.Lab.ptOf_pr hP b _)
    have h2 := E8Fibration.Lab.isSharpBasis_sharpBasis W hW.2 gQ i i'
    simp only [E8Fibration.e8] at h1
    rw [h2] at h1
    exact_mod_cast h1
  refine ⟨bT, fun i => E8Fibration.Lab.ptOf hP b (E8Fibration.Lab.sharpBasis W hW.2 gQ (Pi.single i 1)), htor, ?_, ?_, ?_⟩
  · intro K' _ _ x y hy
    have key := GlobalTheory.symplectic_system_torsion_basis L1 K P' ((l ^ j) ^ 2) z
    revert key
    generalize P'.g = g' at hg ⊢
    subst hg
    intro key
    exact key _ hNK hz htor hpt K' x y hy
  · intro i i'
    rw [hu]
    exact hpt i i'
  · intro a i
    exact hactc act hacts a i

end GlobalTheory.Poinc.Sep.E8Fibration.Lab
end
end
end
