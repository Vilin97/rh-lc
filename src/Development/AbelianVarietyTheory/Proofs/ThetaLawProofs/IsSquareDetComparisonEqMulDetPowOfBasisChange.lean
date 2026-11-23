module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.CardHomVanishingOfDiagBasis
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import Development.AbelianVarietyTheory.Definitions.KeyFormula.DegProd
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.IsSquareDeterminantComparison
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SectionLinCombFiberProductSeparatedStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal

-- Source module: Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsBoxSec

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

noncomputable section
namespace GlobalTheory.BoxDetUnique
variable {X Y Z : Scheme.{0}} {R : Type} [CommRing R]

def kv (q : Z ⟶ Sp R) (z : Z) : R →+* Z.presheaf.stalk z :=
  (Z.presheaf.germ ⊤ z trivial).hom.comp (q.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)

def gsH (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) : Γ(X, U) →+* Y.presheaf.stalk y :=
  (Y.presheaf.germ (f ⁻¹ᵁ U) y h).hom.comp (f.app U).hom

theorem gs_eqH (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a : Γ(X, U)) : gs f y U a = gsH f y U h a :=
  gs_eq f y U h a

theorem gs_sum' (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) {N : Type} (s : Finset N) (a : N → Γ(X, U)) :
    gs f y U (∑ i ∈ s, a i) = ∑ i ∈ s, gs f y U (a i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [gs_eqH f y U h, map_sum]

theorem gs_prod' (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) {N : Type} (s : Finset N) (a : N → Γ(X, U)) :
    gs f y U (∏ i ∈ s, a i) = ∏ i ∈ s, gs f y U (a i) := by
  simp only [gs_eqH f y U h, map_prod]

theorem gs_zero' (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) : gs f y U 0 = 0 := by
  simp only [gs_eqH f y U h, map_zero]

theorem gs_cst (p : Y ⟶ Sp R) (r : Z ⟶ Y) (z : Z) (U : Y.Opens) (h : r z ∈ U) (a : R) :
    gs r z U (cst p U a) = kv (r ≫ p) z a :=
  (gs_res r z le_top h _).trans ((gs_pull r p z ⊤ trivial _).trans (gs_eq (r ≫ p) z ⊤ trivial _))

theorem gen_ratio {K : Type} [Field K] {M : LB X} (hM : M.IsLB) {N : Type} [Fintype N] {φ : N → (Y ⟶ X)} {ε : N → ℤ}
    (p : Y ⟶ Sp K) (hp : Function.Surjective p.appTop.hom)
    {u u' : LB.Gen (LB.LinComb M φ ε)} (hu : u.IsGen) (hu' : u'.IsGen) :
    ∃ c : K, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good M z J →
      (val u' r z J).val = kv (r ≫ p) z c * (val u r z J).val := by
  obtain ⟨t, -, hv⟩ := exists_gen hM (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ h => by
      refine (Fintype.prod_sum_type _).trans (Eq.trans ?_ (Fintype.prod_empty _).symm)
      simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib, mul_inv_cancel])
    (LB.mulGen M _ _ _ _ u' (LB.invGen M _ _ u)) (DVR.mulGen_isGen _ _ _ _ _ _ _ hu' (DVR.invGen_isGen _ _ _ _ hu))
  have le : (⊤ : Y.Opens) ≤ LB.wchart M (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim := fun _ _ =>
    Set.mem_iInter.2 fun k => k.elim
  obtain ⟨a, ha⟩ := hp (res le (t.s PEmpty.elim)).val
  obtain ⟨c, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv).2 a
  refine ⟨c, fun Z r z J hJ => ?_⟩
  have key : (val u' r z J * (val u r z J)⁻¹).val = kv (r ≫ p) z c := by
    rw [← val_inv, ← val_mul hJ, ← hv Z r z J hJ, val_of t r z J PEmpty.elim (fun k => k.elim)]
    exact (congrArg Units.val (gm_res r z le trivial _)).symm.trans ((gs_unit r z ⊤ trivial _).symm.trans
      ((congrArg (gs r z ⊤) ha.symm).trans ((gs_pull r p z ⊤ trivial _).trans (gs_eq (r ≫ p) z ⊤ trivial _))))
  rw [← key, ← Units.val_mul, inv_mul_cancel_right]

theorem gs_sec_pw {L : LB X} {m : ℤ} (s : LB.Sec (pw L m)) (r : Z ⟶ X) (z : Z) (i j : L.ι) (hi : r z ∈ L.U i)
    (hj : r z ∈ L.U j) :
    gs r z (L.U i) (s.f i) = (gm r z (L.U i ⊓ L.U j) (L.g i j) ^ m).val * gs r z (L.U j) (s.f j) := by
  have hm : r z ∈ L.U i ⊓ L.U j := ⟨hi, hj⟩
  refine (gs_res r z _ hm _).symm.trans ((congrArg (gs r z _) (s.compat i j)).trans ((gs_mul r z _ hm _ _).trans
    (congrArg₂ (· * ·) ?_ (gs_res r z _ hm _))))
  exact (gs_unit r z _ hm _).trans (congrArg Units.val (map_zpow _ _ _))

theorem exists_boxSec {L : LB X} {m : ℤ} {N I : Type} [Fintype N] [Fintype I] (φ : N → (Y ⟶ X)) (p : Y ⟶ Sp R)
    (q : I → R) (s : I → N → LB.Sec (pw L m)) : ∃ S : LB.Sec (LB.LinComb L φ (fun _ => m)),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j : N → L.ι), r z ∈ LB.wchart L φ j →
        gs r z (LB.wchart L φ j) (S.f j) =
          ∑ a, kv (r ≫ p) z (q a) * ∏ c, gs (r ≫ φ c) z (L.U (j c)) ((s a c).f (j c)) := by
  obtain ⟨F, hF⟩ : ∃ F : ∀ j : N → L.ι, Γ(Y, LB.wchart L φ j),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j : N → L.ι), r z ∈ LB.wchart L φ j →
        gs r z (LB.wchart L φ j) (F j) =
          ∑ a, kv (r ≫ p) z (q a) * ∏ c, gs (r ≫ φ c) z (L.U (j c)) ((s a c).f (j c)) := by
    refine ⟨fun j => ∑ a, cst p _ (q a) * ∏ c, rs Y (LB.wchart_le L φ j c) (((φ c).app (L.U (j c))).hom ((s a c).f (j c))),
      fun Z r z j h => ?_⟩
    rw [gs_sum' r z _ h]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [gs_mul r z _ h, gs_cst p r z _ h, gs_prod' r z _ h]
    refine congrArg _ (Finset.prod_congr rfl fun c _ => ?_)
    exact (gs_res r z _ h _).trans (gs_pull r (φ c) z _ (LB.wchart_le L φ j c h) _)
  refine ⟨⟨F, fun j j' => fn_ext fun y hy => ?_⟩, hF⟩
  refine (gs_res (𝟙 Y) y _ hy _).trans (Eq.trans ?_ ((gs_mul (𝟙 Y) y _ hy _ _).trans (congrArg₂ (· * ·)
      ((gs_unit (𝟙 Y) y _ hy _).trans (congrArg Units.val (gm_linComb L φ _ (𝟙 Y) y j j' hy.1 hy.2)))
      (gs_res (𝟙 Y) y _ hy _))).symm)
  refine (hF _ (𝟙 Y) y j hy.1).trans (Eq.trans ?_ (congrArg _ (hF _ (𝟙 Y) y j' hy.2)).symm)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [mul_left_comm, Units.coe_prod, ← Finset.prod_mul_distrib]
  refine congrArg _ (Finset.prod_congr rfl fun c _ => ?_)
  exact gs_sec_pw _ _ y _ _ (LB.wchart_le L φ j c hy.1) (LB.wchart_le L φ j' c hy.2)

theorem exists_perm (hN : Out.MulNSt) {K : Type} [Field K] (P : Out.PolAV (Sp K)) (m : ℕ) (al : Matrix (Fin 4) (Fin 4) ℤ)
    (hm : (m : K) ≠ 0) (hal : al.transpose * al = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ))
    (ξ ξ' : (Fin 4 → Fin (m ^ P.g)) → Fin 4 → (𝟙_ (Over (Sp K)) ⟶ P.A))
    (h : Function.Injective ξ) (h' : Function.Injective ξ')
    (e : ∀ I c, (List.ofFn fun r : Fin 4 => ξ I r ^ al r c).prod = 1)
    (e' : ∀ I c, (List.ofFn fun r : Fin 4 => ξ' I r ^ al r c).prod = 1) :
    ∃ σ : Equiv.Perm (Fin 4 → Fin (m ^ P.g)), ξ' = fun I => ξ (σ I) := by
  haveI := P.isAb.comm
  let k := AlgebraicClosure K
  let t : Spec (CommRingCat.of k) ⟶ Sp K := Spec.map (CommRingCat.ofHom (algebraMap K k))
  have hm1 : 1 ≤ m := Nat.pos_of_ne_zero fun h0 => hm (by rw [h0, Nat.cast_zero])
  have hc := GlobalTheory.card_ker_int_matrix_four (Over.mk t ⟶ P.A) m (2 * P.g) al hm1 hal (fun n hn => by
    have hn0 : (n : K) ≠ 0 := fun h0 => hm (by obtain ⟨d, rfl⟩ := hn; rw [Nat.cast_mul, h0, zero_mul])
    refine (hN _ P n (Nat.pos_of_ne_zero fun h0 => hn0 (by rw [h0, Nat.cast_zero]))).2.2.2.2 k t ?_
    rw [← map_natCast (algebraMap K k)]
    exact (map_ne_zero _).2 hn0)
  have hepi : Epi t := by
    haveI : Flat t := by
      rw [HasRingHomProperty.Spec_iff (P := @Flat)]
      exact RingHom.flat_algebraMap_iff.2 inferInstance
    haveI : Surjective t := ⟨fun y => ⟨IsLocalRing.closedPoint k, Subsingleton.elim _ _⟩⟩
    exact Flat.epi_of_flat_of_surjective t
  let f : (𝟙_ (Over (Sp K)) ⟶ P.A) →* (Over.mk t ⟶ P.A) := preHom (toUnit (Over.mk t))
  have hf : Function.Injective f := fun a b hab => by
    have h1 : (toUnit (Over.mk t)).left ≫ a.left = (toUnit (Over.mk t)).left ≫ b.left := congrArg (·.left) hab
    have h2 : (toUnit (Over.mk t)).left = t := (Category.comp_id _).symm.trans (Over.w (toUnit (Over.mk t)))
    haveI : Epi (toUnit (Over.mk t)).left := h2 ▸ hepi
    exact Over.OverMorphism.ext ((cancel_epi _).1 h1)
  have bij : ∀ (ζ : (Fin 4 → Fin (m ^ P.g)) → Fin 4 → (𝟙_ (Over (Sp K)) ⟶ P.A)), Function.Injective ζ →
      (∀ I c, (List.ofFn fun r : Fin 4 => ζ I r ^ al r c).prod = 1) →
      ∃ E : (Fin 4 → Fin (m ^ P.g)) ≃ {ξ : Fin 4 → (Over.mk t ⟶ P.A) // ∀ c, ∏ r', ξ r' ^ al r' c = 1},
        ∀ I r, (E I).1 r = f (ζ I r) := by
    intro ζ hζ he
    let g : (Fin 4 → Fin (m ^ P.g)) → {ξ : Fin 4 → (Over.mk t ⟶ P.A) // ∀ c, ∏ r', ξ r' ^ al r' c = 1} :=
      fun I => ⟨fun r => f (ζ I r), fun c => by
        have := congrArg f (he I c)
        rw [List.prod_ofFn, map_prod, map_one] at this
        simpa only [map_zpow] using this⟩
    have hg : Function.Injective g := fun I I' hI => hζ (funext fun r => hf (congrFun (congrArg Subtype.val hI) r))
    haveI : Finite {ξ : Fin 4 → (Over.mk t ⟶ P.A) // ∀ c, ∏ r', ξ r' ^ al r' c = 1} :=
      Nat.finite_of_card_ne_zero (by rw [hc]; positivity)
    refine ⟨Equiv.ofBijective g (hg.bijective_of_nat_card_le ?_), fun _ _ => rfl⟩
    rw [hc, Nat.card_fun, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_fin, Fintype.card_fin, ← pow_mul]
    exact le_of_eq (by congr 1; ring)
  obtain ⟨E, hE⟩ := bij ξ h e
  obtain ⟨E', hE'⟩ := bij ξ' h' e'
  refine ⟨E'.trans E.symm, funext fun I => funext fun r => hf ?_⟩
  rw [← hE, ← hE']
  simp

theorem det_calc {K : Type} [Field K] {I : Type} [Fintype I] [DecidableEq I] (σ : Equiv.Perm I) (Q Q' T : Matrix I I K)
    (c rho rho' : I → K) (n : ℕ) (hQ : ∀ a b, Q (σ a) b = c a * ∑ d, Q' a d * T b d)
    (hr : ∀ a, rho' a = c a ^ n * rho (σ a)) :
    Q.det ^ (2 * n) * ∏ a, rho a ^ 2 = (Q'.det ^ (2 * n) * ∏ a, rho' a ^ 2) * T.det ^ (2 * n) := by
  have h1 : Q.submatrix σ id = Matrix.diagonal c * (Q' * T.transpose) := by
    ext a b
    rw [Matrix.diagonal_mul, Matrix.mul_apply]
    exact hQ a b
  have h2 := congrArg Matrix.det h1
  rw [Matrix.det_permute, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal] at h2
  have h3 : Q.det ^ 2 = ((∏ a, c a) * (Q'.det * T.det)) ^ 2 := by
    rw [← h2, mul_pow]
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  have h4 : ∏ a, rho' a ^ 2 = (∏ a, c a) ^ (2 * n) * ∏ a, rho a ^ 2 := by
    rw [← Equiv.prod_comp σ (fun a => rho a ^ 2), ← Finset.prod_pow, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun a _ => by rw [hr]; ring
  rw [h4, pow_mul, h3]
  ring

end GlobalTheory.BoxDetUnique
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.DetKroneckerPower

section

@[expose] public section

namespace GlobalTheory

open Kronecker

theorem det_kroneckerPower (R : Type) [CommRing R] (N r : ℕ) (B : Matrix (Fin N) (Fin N) R) :
    (Matrix.of fun (I I' : Fin (r + 1) → Fin N) => ∏ c, B (I c) (I' c)).det
      = B.det ^ ((r + 1) * N ^ r) := by
  induction r with
  | zero =>
    have h : (Matrix.of fun (I I' : Fin (0 + 1) → Fin N) => ∏ c, B (I c) (I' c))
        = B.submatrix (Equiv.funUnique (Fin 1) (Fin N)) (Equiv.funUnique (Fin 1) (Fin N)) := by
      ext I I'
      simp
    rw [h, Matrix.det_submatrix_equiv_self]
    simp
  | succ r ih =>
    have h : (Matrix.of fun (I I' : Fin (r + 1 + 1) → Fin N) => ∏ c, B (I c) (I' c))
        = (B ⊗ₖ (Matrix.of fun (I I' : Fin (r + 1) → Fin N) => ∏ c, B (I c) (I' c))).submatrix
          (Fin.consEquiv (fun _ : Fin (r + 1 + 1) => Fin N)).symm
          (Fin.consEquiv (fun _ : Fin (r + 1 + 1) => Fin N)).symm := by
      ext I I'
      rw [Matrix.of_apply, Fin.prod_univ_succ]
      rfl
    rw [h, Matrix.det_submatrix_equiv_self, Matrix.det_kronecker, ih, ← pow_mul, ← pow_add]
    congr 1
    simp only [Fintype.card_fun, Fintype.card_fin]
    ring

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsSquareDetComparisonEqMulDetPowOfBasisChange

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

noncomputable section
namespace GlobalTheory.BoxDetUnique

theorem isProper_powObj {S : Scheme.{0}} (A : Over S) [GrpObj A] (hA : IsAbelianScheme A) :
    ∀ n, IsProper (Out.powObj A n).hom
  | 0 => inferInstanceAs (IsProper (𝟙 S))
  | n + 1 => (AbelianSchemeGerms.isAbelianScheme_powObj A hA n).proper

theorem box_indep {K : Type} [Field K] (A : Over (Sp K)) [GrpObj A] (hA : IsAbelianScheme A) {L : LB A.left}
    (hL : L.IsLB) {m : ℤ} {N : ℕ} (b : Fin N → LB.Sec (pw L m))
    (hb : ∀ c : Fin N → K, (∀ i, ∑ k, cst A.hom (L.U i) (c k) * (show Γ(A.left, L.U i) from (b k).f i) = 0) → c = 0) :
    ∀ (n : ℕ) (q : (Fin n → Fin N) → K), (∀ (y : (Out.powObj A n).left) J, Good L y J →
      ∑ I, kv (Out.powObj A n).hom y (q I) * ∏ c, gs (Out.powPr A c).left y (L.U (J (Out.powPr A c).left))
        ((b (I c)).f (J (Out.powPr A c).left)) = 0) → q = 0 := by
  intro n
  induction n with
  | zero =>
    intro q hq
    let y : (Out.powObj A 0).left := IsLocalRing.closedPoint K
    choose J hJ using fun χ : (Out.powObj A 0).left ⟶ A.left => exists_chart hL (χ y)
    have := hq y J hJ
    rw [Fintype.sum_unique, Fintype.prod_empty, _root_.mul_one, map_eq_zero] at this
    exact funext fun I => (congrArg q (Subsingleton.elim _ _)).trans this
  | succ n ih =>
    intro q hq
    haveI := hA.proper
    haveI := isProper_powObj A hA n
    choose a ha using fun i : Fin N => exists_boxSec (L := L) (fun _ : Unit => 𝟙 A.left) A.hom (fun _ : Unit => (1 : K))
      (fun _ _ => b i)
    choose d hd using fun i : Fin N => exists_boxSec (L := L) (fun c : Fin n => (Out.powPr A c).left) (Out.powObj A n).hom
      (fun I : Fin n → Fin N => q (Fin.cons i I)) (fun I c => b (I c))
    have H := (GlobalTheory.T.section_lin_comb_fiber_product_separated K _ L hL A (Out.powObj A n) Unit (Fin n) (fun _ => 𝟙 A.left) (fun _ => m)
      (fun c => (Out.powPr A c).left) (fun _ => m)).2 N a d (fun c hc => hb c fun i => fn_ext fun y hy => by
        have hy' : (𝟙 A.left : A.left ⟶ A.left) y ∈ LB.wchart L (fun _ : Unit => 𝟙 A.left) (fun _ => i) :=
          Set.mem_iInter.2 fun _ => hy
        have := congrArg (gs (𝟙 A.left) y (LB.wchart L (fun _ : Unit => 𝟙 A.left) (fun _ => i))) (hc (fun _ => i))
        refine Eq.trans ?_ (((gs_sum' _ y _ hy' _ _).symm.trans this).trans
          ((gs_zero' _ y _ hy').trans (gs_zero' _ y _ hy).symm))
        refine (gs_sum' (𝟙 A.left) y _ hy _ _).trans (Finset.sum_congr rfl fun k _ => ?_)
        refine (gs_mul (𝟙 A.left) y _ hy _ _).trans (Eq.trans ?_ (gs_mul (𝟙 A.left) y _ hy' _ _).symm)
        refine congrArg₂ (· * ·) ((gs_cst A.hom _ y _ hy _).trans (gs_cst A.hom _ y _ hy' _).symm) ?_
        rw [ha k _ _ y _ hy', Fintype.sum_unique, Fintype.prod_unique, map_one, _root_.one_mul, Category.comp_id])
      (fun z J hJ => by
        refine Eq.trans ?_ (hq z J hJ)
        rw [← (Fin.consEquiv fun _ : Fin (n + 1) => Fin N).sum_comp, Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun i _ => ?_
        refine (congrArg₂ (· * ·) (ha i _ _ z _ (hJ.mem _ _)) (hd i _ _ z _ (hJ.mem _ _))).trans ?_
        rw [Fintype.sum_unique, Fintype.prod_unique, map_one, _root_.one_mul, Category.comp_id, Finset.mul_sum]
        refine Finset.sum_congr rfl fun I _ => ?_
        rw [Fin.prod_univ_succ, mul_left_comm, Over.w (snd A (Out.powObj A n))]
        rfl)
    funext I
    have := ih (fun I' => q (Fin.cons (I 0) I')) (fun y J hJ => by
      have h1 := hd (I 0) _ (𝟙 _) y (fun c => J (Out.powPr A c).left) (Set.mem_iInter.2 fun c => hJ _)
      have h0 := h1.symm.trans ((congrArg (gs (𝟙 _) y _) (H _ _)).trans
        (gs_zero' _ y _ (Set.mem_iInter.2 fun c => hJ _)))
      simpa only [Category.id_comp] using h0)
    have h2 := congrFun this (Fin.tail I)
    rwa [Fin.cons_self_tail] at h2

theorem isSquareDetComparison_eq_mul_det_pow_of_basis_change : Out.Laws → ∀ (K : Type) [Field K] (x : KeyIn K) (m : ℕ) (al : Matrix (Fin 4) (Fin 4) ℤ) (b b' : Fin (m ^ x.P.g) → RR x m) (B : (Matrix (Fin (m ^ x.P.g)) (Fin (m ^ x.P.g)) K)ˣ) (lam lam' : Kˣ), (m : K) ≠ 0 → al.transpose * al = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) → IsBasis x b → (∀ k, Coords x b (fun k' => B.val k' k) (b' k).f) → IsSquareDeterminantComparison x m al b lam → IsSquareDeterminantComparison x m al b' lam' → lam' = lam * (Matrix.GeneralLinearGroup.det B) ^ (-8 * (m ^ (3 * x.P.g + 2) : ℕ) : ℤ) := by
  intro laws K _ x m al b b' B lam lam' hm hal hb hB
    ⟨ξ, mu, w, Q, rho, hne, hker, hmu, hw, hn, hQ, hlam⟩ ⟨ξ', mu', w', Q', rho', hne', hker', hmu', hw', hn', hQ', hlam'⟩
  have inj : ∀ ζ : (Fin 4 → Fin (m ^ x.P.g)) → Fin 4 → Pt x,
      (∀ I I', I ≠ I' → ∀ p : Sp K, ∃ r, (ζ I r).left p ≠ (ζ I' r).left p) → Function.Injective ζ := by
    intro ζ h I I' e
    by_contra hI
    obtain ⟨r, hr⟩ := h I I' hI (IsLocalRing.closedPoint K)
    exact hr (by rw [e])
  obtain ⟨σ, rfl⟩ := exists_perm laws.mulN x.P m al hm hal ξ ξ' (inj _ hne) (inj _ hne') hker hker'
  have hL := x.P.isLB
  have hmm : ∀ (Z : Scheme.{0}) (r : Z ⟶ x.P.A.left) (z : Z) (J), Good x.P.L z J → val mu' r z J = val mu r z J := by
    haveI := x.P.isAb.comm
    exact gen_unique hL (S₀ := Sp K) x.P.A.hom (eSec x.P.A) (Over.w η[x.P.A]) (laws.globalFns _ _ x.P.isAb).2 hmu' hmu
      (fun y J hJ => (hn' y J hJ).1.trans (hn y J hJ).1.symm)
  choose c hc using fun I => gen_ratio hL (Out.powObj x.P.A 4).hom
    (laws.globalFns _ _ (AbelianSchemeGerms.isAbelianScheme_powObj _ x.P.isAb 3)).2 (hw (σ I)) (hw' I)
  have hr : ∀ I, (rho' I : K) = c I ^ (m ^ 2) * rho (σ I) := by
    intro I
    let p : (𝟙_ (Over (Sp K))).left := IsLocalRing.closedPoint K
    choose J hJ using fun χ : (𝟙_ (Over (Sp K))).left ⟶ x.P.A.left => exists_chart hL (χ p)
    have h1 := (hn p J hJ).2 (σ I)
    have h2 := (hn' p J hJ).2 I
    simp only [hmm _ _ p J hJ] at h2
    rw [Units.val_mul, Units.val_pow_eq_pow_val, gs_cst _ _ p ⊤ trivial, Category.comp_id] at h1 h2
    rw [hc I _ _ p J hJ, mul_pow, _root_.mul_assoc, h1, ← _root_.mul_assoc, Units.mul_left_inj,
      show eSec (Out.powObj x.P.A 4) ≫ (Out.powObj x.P.A 4).hom = (𝟙_ (Over (Sp K))).hom from Over.w η[Out.powObj x.P.A 4],
      ← map_pow, ← map_mul] at h2
    exact ((kv _ p).injective h2).symm
  have hind := box_indep x.P.A x.P.isAb hL b (fun c hc => by
    obtain ⟨c₀, -, hu⟩ := hb ⟨fun _ => 0, fun i j => by rw [map_zero, map_zero, mul_zero]⟩
    exact (hu c fun i => (hc i).symm).trans (hu 0 fun i =>
      (Finset.sum_eq_zero fun k _ => by rw [Pi.zero_apply, map_zero, zero_mul]).symm).symm) 4
  have hq : ∀ I I', Q (σ I) I' = c I * ∑ d, Q' I d *
      (Matrix.of fun (I I' : Fin (3 + 1) → Fin (m ^ x.P.g)) => ∏ c, B.val (I c) (I' c)) I' d := by
    intro I I'
    refine sub_eq_zero.1 (congrFun (hind (fun I' => Q (σ I) I' - c I * ∑ d, Q' I d *
      (Matrix.of fun (I I' : Fin (3 + 1) → Fin (m ^ x.P.g)) => ∏ c, B.val (I c) (I' c)) I' d) fun y J hJ => ?_) I')
    have h1 := (hQ (σ I) y J hJ).symm.trans (hQ' I y J hJ)
    rw [hc I _ _ y J hJ, mul_comm (kv _ _ _), _root_.mul_assoc, Units.mul_right_inj] at h1
    simp only [gs_cst _ _ y ⊤ trivial, Category.id_comp] at h1
    have h3 : ∀ (r : (Out.powObj x.P.A 4 ⟶ x.P.A)) k, gs r.left y (x.P.L.U (J r.left)) ((b' k).f (J r.left)) =
        ∑ k', kv (Out.powObj x.P.A 4).hom y (B.val k' k) * gs r.left y (x.P.L.U (J r.left)) ((b k').f (J r.left)) := by
      intro r k
      refine (congrArg (gs r.left y (x.P.L.U (J r.left))) (hB k (J r.left))).trans ?_
      refine (gs_sum' _ y _ (hJ _) _ _).trans (Finset.sum_congr rfl fun k' _ => ?_)
      rw [gs_mul _ y _ (hJ _), gs_cst _ _ y _ (hJ _), Over.w r]
    simp only [h3] at h1

    simp only [map_sub, sub_mul, Finset.sum_sub_distrib, h1, map_mul, map_sum, Matrix.of_apply, map_prod,
    _root_.mul_assoc, ← Finset.mul_sum]
    rw [sub_eq_zero]
    congr 1
    simp only [Finset.sum_mul, _root_.mul_assoc]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [← Finset.mul_sum, Finset.prod_univ_sum, Fintype.piFinset_univ]
    simp only [Finset.prod_mul_distrib]
  have key := det_calc σ Q Q' _ c (fun I => rho I) (fun I => rho' I) (m ^ 2) hq hr
  rw [← hlam, ← hlam', GlobalTheory.det_kroneckerPower, ← pow_mul] at key
  have e : lam = lam' * (Matrix.GeneralLinearGroup.det B) ^ (8 * m ^ (3 * x.P.g + 2)) := by
    apply Units.ext
    rw [key, Units.val_mul, Units.val_pow_eq_pow_val]
    congr 2
    ring
  rw [e, _root_.mul_assoc, ← zpow_natCast, ← zpow_add]
  simp

end GlobalTheory.BoxDetUnique
end
end
end
