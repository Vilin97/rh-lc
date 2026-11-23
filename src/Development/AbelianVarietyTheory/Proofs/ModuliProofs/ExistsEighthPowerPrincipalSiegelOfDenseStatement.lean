module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsArBaseAway
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AbelianSchemeEighthPowerOfMatrixAction
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
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CommutatorPairingE8SharpLevelPoints
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DenseE8SharpAfterAdjoiningAllMatricesStatement
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.E8SharpFamilyMatrixRelationsDenseStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LocGenOfTrivial
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSymmetricBiadditiveBundleEighthPowerStatement
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelOnFactorOfEighthPowerAbelianSchemeStatement
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleDiagonalBiadditiveOfE8Form
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelAdjointPrimitiveOfDenseEighthPowersStatement
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilPairingDiagonalBundleOfEighthPowerFormStatement
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.AbelianSchemeEighthPowerOfMatrixActionStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.abelianScheme_eighth_power_of_matrix_action : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (ρ : Matrix (Fin 8) (Fin 8) ℤ → (G ⟶ G)), IsAbelianScheme G → (∀ m, IsMonHom (ρ m)) → (∀ m m', ρ (m * m') = ρ m' ≫ ρ m) → (∀ m m', ρ (m + m') = ρ m * ρ m') → ρ 1 = 𝟙 G → ∃ (A : Over S) (_ : GrpObj A) (pr : Fin 8 → (G ⟶ A)), IsAbelianScheme A ∧ (∀ u, IsMonHom (pr u)) ∧ (∀ (T : Over S) (y : Fin 8 → (T ⟶ A)), ∃! x : T ⟶ G, ∀ u, x ≫ pr u = y u) ∧ ∀ m u, ρ m ≫ pr u = (List.ofFn fun v => pr v ^ m u v).prod := by
  first | exact @GlobalTheory.MatrixPower.abelianScheme_matrix_power | exact GlobalTheory.MatrixPower.abelianScheme_matrix_power | (intros; apply GlobalTheory.MatrixPower.abelianScheme_matrix_power <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.CommutatorPairingE8SharpLevelPointsStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.commutatorPairing_e8Sharp_levelPoints : Out.Laws → ∀ (h g : ℕ) (W : Matrix (Fin 8) (Fin 8) ℤ) (J : Type) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))) (k : ℕ) (o : Type) [CommRing o] (b : TBase o k) (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp o) (t : TObj g k J b s) (A : Over S) [GrpObj A] [IsCommMonObj A] (pr : Fin 8 → (t.A ⟶ A)) (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ A)), IsSharpBasis W bas → (∀ u, IsMonHom (pr u)) → (∀ (T : Over S) (y : Fin 8 → (T ⟶ A)), ∃! x : T ⟶ t.A, ∀ u, x ≫ pr u = y u) → (∀ x y, lev (x + y) = lev x * lev y) → (∀ i u, (t.pt i ≫ pr u).left = (lev (bas (Pi.single i 1) u)).left) → ∀ (K : Type) [Field K] (p : Sp K ⟶ S) (β : o →+* K) (z : Kˣ), p ≫ s = spMap β → (z : K) = β b.ζ → ∀ (X Y : Fin 8 → (Fin h ⊕ Fin h → ℤ)) (y y' : Over.mk p ⟶ t.A), (∀ u, y ≫ pr u = toUnit _ ≫ lev (X u)) → (∀ u, y' ≫ pr u = toUnit _ ≫ lev (Y u)) → Out.WeilIs t.A t.L k y y' (unitOn z ^ ∑ u, ∑ v, (W + W.transpose) u v * omegaStd (X u) (Y v)) := by
  first | exact @GlobalTheory.weilIs_sharp_levelPoints | exact GlobalTheory.weilIs_sharp_levelPoints | (intros; apply GlobalTheory.weilIs_sharp_levelPoints <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqOneOfBiadditiveSliceTrivialEighthPower

section

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.FormBundleKer


open GlobalTheory.CechPic in
theorem eq_one_of_slice_trivial : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ) (S : Scheme.{0}) (G A : Over S) [GrpObj G] [IsCommMonObj G] [GrpObj A] [IsCommMonObj A] (pr : Fin 8 → (G ⟶ A)) (L : LB G.left) (P : LB (G2 A).left), (∀ u, IsMonHom (pr u)) → (∀ (T : Over S) (y : Fin 8 → (T ⟶ A)), ∃! x : T ⟶ G, ∀ u, x ≫ pr u = y u) → L.IsLB → P.IsLB → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → (∀ (T : Over S) (x x' y : T ⟶ A), (∃ t : (LB.LinComb P (K := Fin 3) ![(lift (x * x') y).left, (lift x y).left, (lift x' y).left] ![1, -1, -1]).Gen, t.IsGen) ∧ ∃ t : (LB.LinComb P (K := Fin 3) ![(lift y (x * x')).left, (lift y x).left, (lift y x').left] ![1, -1, -1]).Gen, t.IsGen) → LBIso L (LB.LinComb P (K := Fin 8 × Fin 8) (fun uv => (lift (pr uv.1) (pr uv.2)).left) (fun uv => W uv.1 uv.2)) → Out.KTriv G L → ∀ (T : Over S) (x : T ⟶ A), (∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) → x = 1 := by
  intro W S G A _ _ _ _ pr L P hpr huniv hL hP hsym hbi hLP hK T x hx
  let p : ∀ {T' : Over S}, (T' ⟶ A) → (T' ⟶ A) → Pic T'.left := fun a b => pull (lift a b).left (cls P hP)
  have padd : ∀ {T' : Over S} (a a' b : T' ⟶ A), p (a * a') b = p a b + p a' b := fun {T'} a a' b => by
    have e := (cls_eq_zero_iff (LB.isLB_linComb hP _ _)).2 (hbi T' a a' b).1
    rw [cls_linComb hP, Fin.sum_univ_three] at e
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, one_smul, neg_smul] at e
    rw [← sub_eq_zero, ← e]
    simp only [p]
    abel
  have psym : ∀ {T' : Over S} (a b : T' ⟶ A), p a b = p b a := fun {T'} a b => by
    have e : cls P hP = pull (lift (snd A A) (fst A A)).left (cls P hP) :=
      (cls_eq_iff hP (pull_isLB hP _)).2 hsym
    have k : (lift b a).left ≫ (lift (snd A A) (fst A A)).left = (lift a b).left := by
      rw [← Over.comp_left, comp_lift, lift_fst, lift_snd]
    show pull (lift a b).left (cls P hP) = pull (lift b a).left (cls P hP)
    rw [← k, pull_comp, ← e]
  have pone : ∀ {T' : Over S} (b : T' ⟶ A), p 1 b = 0 := fun b => by
    have := padd 1 1 b
    rw [_root_.mul_one] at this
    exact left_eq_add.1 this
  have px : ∀ {T' : Over S} (τ : T' ⟶ T) (y : T' ⟶ A), p (τ ≫ x) y = 0 := fun τ y => by
    have e := (cls_eq_zero_iff (pull_isLB hP _)).2 hx
    rw [cls_pull hP] at e
    have k : (lift y τ).left ≫ (lift (snd A T ≫ x) (fst A T)).left = (lift (τ ≫ x) y).left := by
      rw [← Over.comp_left, comp_lift, lift_fst, lift_snd_assoc]
    show pull (lift (τ ≫ x) y).left (cls P hP) = 0
    rw [← k, pull_comp, e, map_zero]
  have hl : ∀ {T' : Over S} (z : T' ⟶ G), pull z.left (cls L hL) =
      ∑ uv : Fin 8 × Fin 8, W uv.1 uv.2 • p (z ≫ pr uv.1) (z ≫ pr uv.2) := fun z => by
    have e := (cls_eq_iff hL (LB.isLB_linComb hP _ _)).2 hLP
    rw [cls_linComb hP] at e

    rw [e, map_sum]
    refine Finset.sum_congr rfl fun uv _ => ?_
    rw [map_zsmul, ← pull_comp, ← Over.comp_left, comp_lift]
  obtain ⟨x', hx', -⟩ := huniv T fun v => if v = 0 then x else 1
  have pz : ∀ u (y : T ⊗ G ⟶ A), p ((fst T G ≫ x') ≫ pr u) y = 0 := fun u y => by
    rw [Category.assoc, hx']
    split_ifs
    · exact px _ _
    · rw [MonObj.comp_one]; exact pone _
  have key : pull (Out.translPt G x').left (cls L hL) = pull (snd T G).left (cls L hL) := by
    have e : Out.translPt G x' = (fst T G ≫ x') * snd T G := rfl
    rw [hl, hl, e]
    refine Finset.sum_congr rfl fun uv _ => ?_
    have := hpr uv.1
    have := hpr uv.2
    rw [MonObj.mul_comp, MonObj.mul_comp, padd, pz, zero_add, psym, padd, pz, zero_add, psym]
  have H : KerPow.HasGen L (K := Fin 2) ![(Out.translPt G x').left, (snd T G).left] ![1, -1] := by
    refine (cls_eq_zero_iff (LB.isLB_linComb hL _ _)).1 ?_
    rw [cls_linComb hL, Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, key, one_smul, neg_smul, add_neg_cancel]
  have h1 : x' = 1 := KerPow.eq_one_of_locGen hK x' fun _ => ⟨⊤, trivial, H.pull _ fun _ => rfl⟩
  have h0 := hx' 0
  have := hpr 0
  rw [h1, MonObj.one_comp, if_pos rfl] at h0
  exact h0.symm

end GlobalTheory.FormBundleKer
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqOneOfBiadditiveSliceTrivialEighthPowerStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.eq_one_of_biadditive_slice_trivial_eighthPower : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ) (S : Scheme.{0}) (G A : Over S) [GrpObj G] [IsCommMonObj G] [GrpObj A] [IsCommMonObj A] (pr : Fin 8 → (G ⟶ A)) (L : LB G.left) (P : LB (G2 A).left), (∀ u, IsMonHom (pr u)) → (∀ (T : Over S) (y : Fin 8 → (T ⟶ A)), ∃! x : T ⟶ G, ∀ u, x ≫ pr u = y u) → L.IsLB → P.IsLB → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → (∀ (T : Over S) (x x' y : T ⟶ A), (∃ t : (LB.LinComb P (K := Fin 3) ![(lift (x * x') y).left, (lift x y).left, (lift x' y).left] ![1, -1, -1]).Gen, t.IsGen) ∧ ∃ t : (LB.LinComb P (K := Fin 3) ![(lift y (x * x')).left, (lift y x).left, (lift y x').left] ![1, -1, -1]).Gen, t.IsGen) → LBIso L (LB.LinComb P (K := Fin 8 × Fin 8) (fun uv => (lift (pr uv.1) (pr uv.2)).left) (fun uv => W uv.1 uv.2)) → Out.KTriv G L → ∀ (T : Over S) (x : T ⟶ A), (∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) → x = 1 := by
  first | exact @GlobalTheory.FormBundleKer.eq_one_of_slice_trivial | exact GlobalTheory.FormBundleKer.eq_one_of_slice_trivial | (intros; apply GlobalTheory.FormBundleKer.eq_one_of_slice_trivial <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleDiagonalBiadditiveOfE8FormStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.relAmple_diagonal_biadditive_of_e8Form : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ) (S : Scheme.{0}) [IsLocallyNoetherian S] (G A : Over S) [GrpObj G] [IsCommMonObj G] [GrpObj A] [IsCommMonObj A] (pr : Fin 8 → (G ⟶ A)) (L : LB G.left) (P : LB (G2 A).left), IsE8 W → IsAbelianScheme G → IsAbelianScheme A → (∀ u, IsMonHom (pr u)) → (∀ (T : Over S) (y : Fin 8 → (T ⟶ A)), ∃! x : T ⟶ G, ∀ u, x ≫ pr u = y u) → L.IsLB → P.IsLB → (∀ (T : Over S) (x x' y : T ⟶ A), (∃ t : (LB.LinComb P (K := Fin 3) ![(lift (x * x') y).left, (lift x y).left, (lift x' y).left] ![1, -1, -1]).Gen, t.IsGen) ∧ ∃ t : (LB.LinComb P (K := Fin 3) ![(lift y (x * x')).left, (lift y x).left, (lift y x').left] ![1, -1, -1]).Gen, t.IsGen) → LBIso L (LB.LinComb P (K := Fin 8 × Fin 8) (fun uv => (lift (pr uv.1) (pr uv.2)).left) (fun uv => W uv.1 uv.2)) → Out.RelAmple G L → Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) := by
  first | exact @GlobalTheory.PowerForm.relAmple_diag | exact GlobalTheory.PowerForm.relAmple_diag | (intros; apply GlobalTheory.PowerForm.relAmple_diag <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsEighthPowerPrincipalSiegelOfDense

section

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.SharpFamily

theorem exists_isSharp_of_dense : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (h g : ℕ) (W : Matrix (Fin 8) (Fin 8) ℤ) (J : Type) (a : J → Matrix (Fin 8) (Fin 8) ℤ) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))), IsE8 W → IsSharpBasis W bas → (∀ u v, ∃ j, a j = Matrix.single u v 1) → ∀ (k : ℕ) (o : Type) [CommRing o] (b : TBase o k) (em : o →+* ℂ) (S : Scheme.{0}) [IsLocallyNoetherian S] [IsReduced S] (s : S ⟶ Sp o) (t : TObj g k J b s), Odd k → Dense (fromSet em (SharpClass (b := b) W a bas em) t) → ∃ c : SiegPre h k (b.ζ : o) s, c.Principal ∧ IsSharp W a bas t c := by
  intro laws _ cube h g W J a bas hW hbas hunit k o _ b em S _ _ s t₀ hk hd₀
  obtain ⟨t, hd, back⟩ := GlobalTheory.T.dense_e8Sharp_after_adjoining_all_matrices h g W J a bas k o b em S s t₀ hunit hd₀
  obtain ⟨rmul, radd, rone, rpt⟩ := GlobalTheory.T.dense_fromSet_sharpClass h g W _ _ bas k o b em S s t hd
  obtain ⟨adj, diag⟩ := GlobalTheory.T.thetaLevel_adjoint_primitive_of_dense_eighth_powers laws.globalFns cube h g W _ _ bas k o b em S s t hd
  letI := t.ab.comm
  let ρ : Matrix (Fin 8) (Fin 8) ℤ → (t.A ⟶ t.A) := fun m => t.act (Sum.inr m)
  obtain ⟨A, _, pr, hA, hpr, hprod, hρ⟩ := GlobalTheory.T.abelianScheme_eighth_power_of_matrix_action S t.A ρ t.ab (fun m => t.hom _)
    (fun m m' => rmul (Sum.inr m) (Sum.inr m') (Sum.inr _) rfl) (fun m m' => radd (Sum.inr m) (Sum.inr m') (Sum.inr _) rfl)
    (rone (Sum.inr 1) rfl)
  letI := hA.comm
  obtain ⟨P, hP, r₁, r₂, hsym, hbi, hiso⟩ := GlobalTheory.T.exists_symmetric_biadditive_bundle_eighthPower W S t.A A pr t.L ρ hW hpr hprod t.isLB
    (cube S t.pol t.L t.isLB) hρ (fun m m' e => adj (Sum.inr m) (Sum.inr m') e) (fun m e => diag (Sum.inr m) e)
  let pt : Fin (2 * g) → (𝟙_ (Over S) ⟶ t.A) := fun i => Over.homMk (t.pt i).left (Over.w (t.pt i))
  let lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ A) := fun x =>
    (∏ i, pt i ^ bas.symm (Pi.single 0 x) i) ≫ pr 0
  have hadd : ∀ x y, lev (x + y) = lev x * lev y := fun x y => by
    have := hpr 0
    simp only [lev, Pi.single_add, map_add (f := _), Pi.add_apply, zpow_add, Finset.prod_mul_distrib, MonObj.mul_comp]
  have hpt : ∀ i u, (t.pt i ≫ pr u).left = (lev (bas (Pi.single i 1) u)).left := fun i u => by
    have e₁ : ρ (Matrix.single 0 u 1) ≫ pr 0 = pr u := by
      rw [hρ, List.prod_ofFn, Finset.prod_eq_single u] <;> simp +contextual [Matrix.single_apply, eq_comm]
    have e₂ := rpt (Sum.inr (Matrix.single 0 u 1)) i
    have e₃ : (fun u' => ∑ v, (Sum.elim a id (Sum.inr (Matrix.single 0 u 1)) : Matrix (Fin 8) (Fin 8) ℤ) u' v •
        bas (Pi.single i 1) v) = Pi.single 0 (bas (Pi.single i 1) u) := by
      funext u'
      by_cases hu : u' = 0
      · subst hu
        simp [Matrix.single_apply]
      · simp [Matrix.single_apply, hu, Ne.symm hu]
    rw [e₃, List.prod_ofFn] at e₂
    rw [← e₁, ← Category.assoc, e₂]
    rfl
  obtain ⟨htor, hgeo⟩ := GlobalTheory.T.level_on_factor_of_eighth_power_abelianScheme h g _ bas k o b S s t A pr lev hk.pos hpr hprod hadd hpt
  refine ⟨{ A := A, ab := hA, P := P, isLB := hP, rig₁ := r₁, rig₂ := r₂, symm := hsym, lev := lev, lev_add := hadd,
            lev_tors := htor, geom := fun K _ _ p β z hp hz => ⟨(hgeo K p).1, (hgeo K p).2, fun x y => ?_⟩ },
    ⟨GlobalTheory.T.relAmple_diagonal_biadditive_of_e8Form W S t.A A pr t.L P hW t.ab hA hpr hprod t.isLB hP hbi hiso t.ample,
      GlobalTheory.T.eq_one_of_biadditive_slice_trivial_eighthPower W S t.A A pr t.L P hpr hprod t.isLB hP hsym hbi hiso t.ktriv⟩,
    back _ ⟨pr, hpr, hprod, hiso, fun j u => ?_, hpt⟩⟩
  · have e : unitOn (z ^ (2 * omegaStd x y)) = unitOn z ^ (2 * omegaStd x y) := map_zpow (Units.map _) _ _
    rw [e]
    exact GlobalTheory.T.weilPairing_diagonal_bundle_of_eighthPower_form laws.globalFns h k W S t.A A pr t.L P K p (fun x => toUnit _ ≫ lev x) (unitOn z) hW t.ab hA
      hpr hprod t.isLB hP hsym hbi hiso (fun x y => by rw [hadd, MonObj.comp_mul])
      (fun x => by rw [← MonObj.comp_pow, htor, MonObj.comp_one])
      (GlobalTheory.T.commutatorPairing_e8Sharp_levelPoints laws h g W _ bas k o b S s t A pr lev hbas hpr hprod hadd hpt K p β z hp hz) x y
  · rw [rmul (Sum.inr (Sum.elim a id j)) (Sum.inr 1) j (_root_.mul_one _).symm, rone (Sum.inr 1) rfl, Category.id_comp]
    exact hρ _ u

end GlobalTheory.SharpFamily
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsEighthPowerPrincipalSiegelOfDenseStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.exists_eighthPower_principalSiegel_of_dense : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (h g : ℕ) (W : Matrix (Fin 8) (Fin 8) ℤ) (J : Type) (a : J → Matrix (Fin 8) (Fin 8) ℤ) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))), IsE8 W → IsSharpBasis W bas → (∀ u v, ∃ j, a j = Matrix.single u v 1) → ∀ (k : ℕ) (o : Type) [CommRing o] (b : TBase o k) (em : o →+* ℂ) (S : Scheme.{0}) [IsLocallyNoetherian S] [IsReduced S] (s : S ⟶ Sp o) (t : TObj g k J b s), Odd k → Dense (fromSet em (SharpClass (b := b) W a bas em) t) → ∃ c : SiegPre h k (b.ζ : o) s, c.Principal ∧ IsSharp W a bas t c := by
  first | exact @GlobalTheory.SharpFamily.exists_isSharp_of_dense | exact GlobalTheory.SharpFamily.exists_isSharp_of_dense | (intros; apply GlobalTheory.SharpFamily.exists_isSharp_of_dense <;> assumption)
end
end
