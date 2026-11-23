module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ToricPeriodBlockIsSymm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalisedMultiplicationPullbackFunctionStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymLiftTorsionPointClassicalActionStatement
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.MemSpanOfCardLe
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.EllipsoidStA
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaCharEntireNeZeroAutomorphy
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SurjectiveOfComplexPointsLiftOfUniversallyClosed
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.IsReducedSchemeOfSmoothOfIsIntegrallyClosed
import Mathlib.Tactic.Basify

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionValueTangentLiftEqFirstJet

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix
open Filter Topology

noncomputable section

namespace GlobalTheory.MBLow.EpsVal

open GlobalTheory.TangentOrigin

theorem valR_comp_eq {R : Type} [CommRing R] {X Y : Scheme.{0}} (x : Sp R ⟶ X) (s : X ⟶ Y) (U : X.Opens) (V : Y.Opens)
    (e : U ≤ s ⁻¹ᵁ V) (h : ⊤ ≤ x ⁻¹ᵁ U) (a : Γ(Y, V)) :
    valR (x ≫ s) V a = evalPt x U h ((s.appLE V U e).hom a) := by
  have h' : ⊤ ≤ (x ≫ s) ⁻¹ᵁ V := fun p hp => e (h hp)
  unfold valR evalPt
  rw [dite_eq_left h', ← Scheme.Hom.appLE_comp_appLE x s V U ⊤ e h]
  rfl

def sec (A : Over (Sp ℂ)) : A ⟶ baseOver (Sp ℂ) ⊗ A :=
  lift (Over.homMk A.hom (by simp) : A ⟶ baseOver (Sp ℂ)) (𝟙 A)

theorem sec_snd (A : Over (Sp ℂ)) : (sec A).left ≫ (snd (baseOver (Sp ℂ)) A).left = 𝟙 A.left := by
  rw [← Over.comp_left, sec, lift_snd, Over.id_left]

theorem epsLift_eq {A : Over (Sp ℂ)} (v : epsR ℂ ⟶ A) : epsLift v = v.left ≫ (sec A).left := by
  rw [← Over.comp_left, sec, comp_lift, Category.comp_id, epsLift]
  congr 2
  ext
  simp

theorem ptSecT_eq {A : Over (Sp ℂ)} (z : baseOver (Sp ℂ) ⟶ A) :
    (ptSecT A z).left = z.left ≫ (sec A).left := by
  rw [← Over.comp_left, sec, comp_lift, Category.comp_id, ptSecT]
  congr 2
  ext
  simpa using (Over.w z).symm

theorem le_sec {A : Over (Sp ℂ)} (L : LB A.left) (k : ℤ) (i : L.ι) :
    L.U i ≤ (sec A).left ⁻¹ᵁ ((LPow A L k (baseOver (Sp ℂ))).U fun _ => i) := by
  intro p hp
  refine Set.mem_iInter.2 fun _ => ?_
  change ((sec A).left ≫ (snd (baseOver (Sp ℂ)) A).left) p ∈ L.U i
  rw [sec_snd]
  exact hp

theorem valR_epsLift : ∀ (g : ℕ) (P : PolAV (Sp ℂ)) (u : HolUnif P.A P.L g) (k : ℕ) (t : LB.Sec (LPow P.A P.L (k : ℤ) (baseOver (Sp ℂ)))) (f : (Fin g → ℂ) → ℂ) (v : epsR ℂ ⟶ P.A) (W : Fin g → ℂ) (i : P.L.ι), FnT u k t f → Differentiable ℂ f → IsTangent v → u.IsDiff W v → ⊤ ≤ (eSec P.A) ⁻¹ᵁ P.L.U i → valR (epsLift v) ((LPow P.A P.L (k : ℤ) (baseOver (Sp ℂ))).U fun _ => i) (t.f fun _ => i) = TrivSqZeroExt.inl (u.fr i 0 ^ k) * (TrivSqZeroExt.inl (f 0) + TrivSqZeroExt.inr (fderiv ℂ f 0 W + (k * fderiv ℂ (u.fr i) 0 W / u.fr i 0) * f 0)) := by
  intro g P u k t f v W i hf hd hv hW hi
  have h0 : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ P.L.U i := by
    rw [ex_zero_left]; exact hi
  have h : ⊤ ≤ v.left ⁻¹ᵁ P.L.U i := (tangent_mem_iff (u := u) hv _).2 h0
  set a := ((sec P.A).left.appLE _ _ (le_sec P.L (k : ℤ) i)).hom (t.f fun _ => i) with ha
  have hval : ∀ z (hz : ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U i),
      evalPt (R := ℂ) (u.ex z).left (P.L.U i) hz a = f z * u.fr i z ^ k := by
    intro z hz
    have := hf i z hz
    rw [ptSecT_eq] at this
    exact (valR_comp_eq (R := ℂ) (u.ex z).left (sec P.A).left _ _ (le_sec P.L (k : ℤ) i) hz _).symm.trans this
  have hev : (fun z => valAt' (u.ex z).left (P.L.U i) a) =ᶠ[𝓝 0] fun z => f z * u.fr i z ^ k := by
    filter_upwards [eventually_mem u h0] with z hz
    rw [valAt'_eq_evalPt _ _ hz, hval z hz]
  have hfr : DifferentiableAt ℂ (u.fr i) 0 := (u.fr_hol i).differentiableAt (eventually_mem u h0)
  have hne : u.fr i 0 ≠ 0 := u.fr_ne i 0 h0
  have hD := ((hd 0).hasFDerivAt.mul (hfr.hasFDerivAt.pow k)).fderiv
  rw [epsLift_eq]
  refine (valR_comp_eq (R := DualNumber ℂ) v.left (sec P.A).left _ _ (le_sec P.L (k : ℤ) i) h _).trans ?_
  refine TrivSqZeroExt.ext ?_ ?_
  · refine (tangent_fst (u := u) hv h h0 a).trans ?_
    rw [hval 0 h0]
    simp [mul_comm]
  · refine (hW _ h a).trans ?_
    rw [hev.fderiv_eq]
    refine (congrArg (fun φ => φ W) hD).trans ?_
    rcases k with _ | k
    · simp
    · simp
      field_simp
      ring

end GlobalTheory.MBLow.EpsVal

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionValueTangentLiftEqFirstJetStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

theorem _root_.GlobalTheory.T.sectionValue_tangentLift_eq_firstJet : ∀ (g : ℕ) (P : PolAV (Sp ℂ)) (u : HolUnif P.A P.L g) (k : ℕ) (t : LB.Sec (LPow P.A P.L (k : ℤ) (baseOver (Sp ℂ)))) (f : (Fin g → ℂ) → ℂ) (v : epsR ℂ ⟶ P.A) (W : Fin g → ℂ) (i : P.L.ι), FnT u k t f → Differentiable ℂ f → IsTangent v → u.IsDiff W v → ⊤ ≤ (eSec P.A) ⁻¹ᵁ P.L.U i → valR (epsLift v) ((LPow P.A P.L (k : ℤ) (baseOver (Sp ℂ))).U fun _ => i) (t.f fun _ => i) = TrivSqZeroExt.inl (u.fr i 0 ^ k) * (TrivSqZeroExt.inl (f 0) + TrivSqZeroExt.inr (fderiv ℂ f 0 W + (k * fderiv ℂ (u.fr i) 0 W / u.fr i 0) * f 0)) := by
  first | exact @GlobalTheory.MBLow.EpsVal.valR_epsLift | exact GlobalTheory.MBLow.EpsVal.valR_epsLift | (intros; apply GlobalTheory.MBLow.EpsVal.valR_epsLift <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSectionInverseImageBaseProductFunction

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

noncomputable section

namespace GlobalTheory.MBLow.Cl

theorem lpow_le {S : Scheme.{0}} (P : PolAV S) (T : Over S) (k : ℤ) (j : Fin 1 → P.L.ι) :
    (LPow P.A P.L k T).U j ≤ (snd T P.A).left ⁻¹ᵁ P.L.U (j 0) :=
  LB.wchart_le P.L (fun _ : Fin 1 => (snd T P.A).left) j 0

theorem appLE_swap {X Y : Scheme.{0}} (φ : Y ⟶ X) {U U' : X.Opens} {V V' : Y.Opens} (h : V ≤ φ ⁻¹ᵁ U) (h' : V' ≤ φ ⁻¹ᵁ U')
    (a : V' ≤ V) (b : U' ≤ U) (f : Γ(X, U)) :
    (Y.presheaf.map (homOfLE a).op).hom ((φ.appLE U V h).hom f) =
      (φ.appLE U' V' h').hom ((X.presheaf.map (homOfLE b).op).hom f) := by
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]

theorem linComb_g_one {X Y : Scheme.{0}} (L : LB X) (φ : Y ⟶ X) (i j : Fin 1 → L.ι) :
    ((LB.LinComb L (fun _ : Fin 1 => φ) (fun _ => ((1 : ℕ) : ℤ))).g i j).val =
      (φ.appLE (L.U (i 0) ⊓ L.U (j 0)) (LB.wchart L (fun _ : Fin 1 => φ) i ⊓ LB.wchart L (fun _ : Fin 1 => φ) j)
        (le_inf (inf_le_left.trans (LB.wchart_le L (fun _ : Fin 1 => φ) i 0))
          (inf_le_right.trans (LB.wchart_le L (fun _ : Fin 1 => φ) j 0)))).hom (L.g (i 0) (j 0)).val := by
  unfold LB.LinComb
  dsimp only
  rw [Fin.prod_univ_one, Nat.cast_one, zpow_one]
  rfl

def pullSec1 {S : Scheme.{0}} (P : PolAV S) (T : Over S) (s : P.L.Sec) :
    LB.Sec (LPow P.A P.L ((1 : ℕ) : ℤ) T) where
  f j := ((snd T P.A).left.appLE _ _ (lpow_le P T _ j)).hom (s.f (j 0))
  compat i j := by
    have h := congrArg ((snd T P.A).left.appLE (P.L.U (i 0) ⊓ P.L.U (j 0))
      ((LPow P.A P.L ((1 : ℕ) : ℤ) T).U i ⊓ (LPow P.A P.L ((1 : ℕ) : ℤ) T).U j)
      (le_inf (inf_le_left.trans (lpow_le P T _ i)) (inf_le_right.trans (lpow_le P T _ j)))).hom (s.compat (i 0) (j 0))
    rw [map_mul] at h
    refine (appLE_swap _ _ _ _ _ _).trans (h.trans (congrArg₂ (· * ·) ?_ (appLE_swap _ _ _ _ _ _).symm))
    exact (linComb_g_one P.L (snd T P.A).left i j).symm

theorem pullbackSectionToBaseChangedAbelian_isInverseImage {S : Scheme.{0}} (P : PolAV S) (T : Over S) (s : P.L.Sec) : IsPolAVSectionInverseImage P T s (pullSec1 P T s) :=
  fun _ _ => rfl

theorem ptSecT_snd' {S : Scheme.{0}} (A : Over S) [GrpObj A] {T : Over S} (z : T ⟶ A) :
    (ptSecT A z).left ≫ (snd T A).left = z.left := by
  rw [← Over.comp_left, ptSecT, lift_snd]

theorem valR_appLE' {R : Type} [CommRing R] {X Y : Scheme.{0}} (x : Sp R ⟶ Y) (φ : Y ⟶ X) (U : X.Opens) (V : Y.Opens)
    (h : V ≤ φ ⁻¹ᵁ U) (hx : ⊤ ≤ x ⁻¹ᵁ V) (f : Γ(X, U)) :
    valR x V ((φ.appLE U V h).hom f) = valR (x ≫ φ) U f := by
  have h' : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ U := fun p hp => h (hx hp)
  rw [valR, valR, dite_eq_left hx, dite_eq_left h', ← CommRingCat.comp_apply (φ.appLE U V h), Scheme.Hom.appLE_comp_appLE]

theorem valR_eq_valAt' {X : Scheme.{0}} (x : Sp ℂ ⟶ X) (U : X.Opens) (f : Γ(X, U)) : valR x U f = valAt' x U f := by
  unfold valR valAt' valAt
  congr

theorem powerSectionFunctionInFrame_of_inverseImage {P : PolAV (Sp ℂ)} {g : ℕ} (u : HolUnif P.A P.L g) (s : P.L.Sec) (θ) (h : u.IsFn s θ)
    (th) (H : IsPolAVSectionInverseImage P (baseOver (Sp ℂ)) s th) : FnT u 1 th θ := by
  intro i z hz
  have e := ptSecT_snd' P.A (T := baseOver (Sp ℂ)) (u.ex z)
  have hx : ⊤ ≤ (ptSecT P.A (T := baseOver (Sp ℂ)) (u.ex z)).left ⁻¹ᵁ
      (LPow P.A P.L ((1 : ℕ) : ℤ) (baseOver (Sp ℂ))).U (fun _ => i) := fun p hp =>
    val_le P.A P.L (T := baseOver (Sp ℂ)) (u.ex z) (fun _ => i) (Set.mem_iInter.2 fun _ => hz hp)
  rw [H i (lpow_le P _ _ fun _ => i), pow_one, ← h i z hz, ← valR_eq_valAt']
  refine (valR_appLE' _ _ _ _ _ hx _).trans ?_
  exact congrArg (fun y => valR y (P.L.U i) (s.f i)) e

theorem eq_of_fnT {P : PolAV (Sp ℂ)} {g : ℕ} (u : HolUnif P.A P.L g) (k : ℕ)
    (t t' : LB.Sec (LPow P.A P.L (k : ℤ) (baseOver (Sp ℂ)))) (f) (h : FnT u k t f) (h' : FnT u k t' f) (j) :
    t.f j = t'.f j := by
  obtain ⟨i, rfl⟩ : ∃ i : P.L.ι, j = fun _ => i := ⟨j 0, funext fun a => congrArg j (Subsingleton.elim _ _)⟩
  have hp : (baseOver (Sp ℂ) ⊗ P.A).hom = pullback.fst (𝟙 (Sp ℂ)) P.A.hom := Category.comp_id _
  have := P.isAb.smooth
  have : Smooth (baseOver (Sp ℂ) ⊗ P.A).hom := by rw [hp]; infer_instance
  have := isReduced_of_smooth_complex _ (baseOver (Sp ℂ) ⊗ P.A).hom inferInstance
  refine ComplexPoints.eq_of_valAt'_eq (baseOver (Sp ℂ) ⊗ P.A).hom _ _ _ fun x hx hi => ?_
  let x' : baseOver (Sp ℂ) ⟶ baseOver (Sp ℂ) ⊗ P.A := Over.homMk x hx
  obtain ⟨z, hz⟩ := u.ex_onto (x' ≫ snd _ _)
  have e : ptSecT P.A (T := baseOver (Sp ℂ)) (u.ex z) = x' := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [ptSecT, lift_fst]
      refine Over.OverMorphism.ext ?_
      exact ((Category.comp_id _).symm.trans (Over.w (x' ≫ fst _ _))).symm
    · rw [ptSecT, lift_snd]; exact hz
  obtain rfl : (ptSecT P.A (T := baseOver (Sp ℂ)) (u.ex z)).left = x := congrArg (·.left) e
  have hz' : ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U i := by
    intro p hp
    have := lpow_le P _ (k : ℤ) (fun _ => i) (hi hp)
    rw [← ptSecT_snd' P.A (T := baseOver (Sp ℂ)) (u.ex z)]
    exact this
  rw [← valR_eq_valAt', ← valR_eq_valAt']
  exact (h i z hz').trans (h' i z hz').symm

theorem thetaSection_fnT_thetaChar_and_unique : ∀ (g : ℕ) (x : KeyIn ℂ) (hg : x.P.g = g) (u : HolUnif x.P.A x.P.L g) (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (c : ℂ) (W : Fin g → Fin g → ℂ), NF x hg u τ a b c W → (∃ th, IsPolAVSectionInverseImage x.P (baseOver (Sp ℂ)) x.th th) ∧ (∀ th, IsPolAVSectionInverseImage x.P (baseOver (Sp ℂ)) x.th th → FnT u 1 th fun z => c * thetaChar τ a b z) ∧ ∀ (k : ℕ) (t t' : LB.Sec (LPow x.P.A x.P.L (k : ℤ) (baseOver (Sp ℂ)))) f, FnT u k t f → FnT u k t' f → ∀ j, t.f j = t'.f j :=
  fun _ x _ u _ _ _ _ _ h => ⟨⟨_, pullbackSectionToBaseChangedAbelian_isInverseImage x.P _ x.th⟩, powerSectionFunctionInFrame_of_inverseImage u x.th _ h.2.2.2.2.2.2.2.1,
    fun k t t' f => eq_of_fnT u k t t' f⟩

end GlobalTheory.MBLow.Cl

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSectionInverseImageBaseProductFunctionStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

theorem _root_.GlobalTheory.T.thetaSection_inverseImage_baseProduct_function : ∀ (g : ℕ) (x : KeyIn ℂ) (hg : x.P.g = g) (u : HolUnif x.P.A x.P.L g) (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (c : ℂ) (W : Fin g → Fin g → ℂ), NF x hg u τ a b c W → (∃ th, IsPolAVSectionInverseImage x.P (baseOver (Sp ℂ)) x.th th) ∧ (∀ th, IsPolAVSectionInverseImage x.P (baseOver (Sp ℂ)) x.th th → FnT u 1 th fun z => c * thetaChar τ a b z) ∧ ∀ (k : ℕ) (t t' : LB.Sec (LPow x.P.A x.P.L (k : ℤ) (baseOver (Sp ℂ)))) f, FnT u k t f → FnT u k t' f → ∀ j, t.f j = t'.f j := by
  first | exact @GlobalTheory.MBLow.Cl.thetaSection_fnT_thetaChar_and_unique | exact GlobalTheory.MBLow.Cl.thetaSection_fnT_thetaChar_and_unique | (intros; apply GlobalTheory.MBLow.Cl.thetaSection_fnT_thetaChar_and_unique <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThJetOfNormalForm

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

namespace GlobalTheory.MBLow.Cl

theorem exists_chart_origin (P : PolAV (Sp ℂ)) : ∃ i : P.L.ι, ⊤ ≤ (eSec P.A) ⁻¹ᵁ P.L.U i := by
  have hc := P.isLB.cover
  let p : (Sp ℂ) := default
  have hp : (eSec P.A) p ∈ (⨆ i, P.L.U i) := by rw [hc]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hp
  refine ⟨i, fun q _ => ?_⟩
  have : q = p := Subsingleton.elim (α := Sp ℂ) _ _
  rw [this]; exact hi

theorem differentiable_trF {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (m : ℕ) (M N : Fin g → ℤ)
    (h : Differentiable ℂ (thetaChar τ a b)) : Differentiable ℂ (trF τ a b m M N) := by
  unfold trF trFac
  refine Differentiable.mul ?_ (h.comp (by fun_prop))
  refine Differentiable.cexp ?_
  simp only [dotProduct]
  fun_prop

theorem thJet_of_normalForm : ∀ (g : ℕ) (x : KeyIn ℂ) (hg : x.P.g = g) (u : HolUnif x.P.A x.P.L g) (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (c : ℂ) (W : Fin g → Fin g → ℂ), NF x hg u τ a b c W → ∀ m : ℕ, Odd m → ∀ (I : Type) (M N : I → Fin g → ℤ) (pt : I → ((baseOver (Sp ℂ)) ⟶ x.P.A)), (∀ i, (pt i).left = (u.ex (((m : ℂ) ^ 2)⁻¹ • perV τ (M i) (N i))).left) → ∀ e : Fin g → ℂ, ThJet x hg m pt (fun i => c * trF τ a b m (M i) (N i) 0) (fun i j => c * fderiv ℂ (trF τ a b m (M i) (N i)) 0 (W j) + e j * (c * trF τ a b m (M i) (N i) 0)) := by
  intro g x hg u τ a b c W hNF m hm I M N pt hpt e
  obtain ⟨⟨th, hth⟩, hfn, -⟩ := GlobalTheory.T.thetaSection_inverseImage_baseProduct_function g x hg u τ a b c W hNF
  obtain ⟨α, s₁, hα, hcorr, htw, hs₁⟩ := GlobalTheory.T.exists_normalised_multiplicationPullback_function g x hg u τ a b c W hNF m th _ (hfn th hth)
  have hU := fun i => GlobalTheory.T.exists_symLift_torsionPoint_classical_action g x hg u τ a b c W hNF m hm (M i) (N i) (pt i) (hpt i)
  choose U hUs hUa using hU
  have ht := fun i => hUa i s₁ _ hs₁
  choose t hta htf using ht
  obtain ⟨hsy, hpos, ha, hb, hc, hΛ, hrig, hFn, hdiff⟩ := hNF
  obtain ⟨i₀, hi₀⟩ := exists_chart_origin x.P
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm.pos.ne'
  have hθ := (thetaChar_entire_ne_zero_automorphy g τ a b hsy hpos ha hb).1
  have hF : ∀ i, (fun z => trFac τ a b m (M i) (N i) z * (c * thetaChar τ a b
      ((m : ℂ) • (z + ((m : ℂ) ^ 2)⁻¹ • perV τ (M i) (N i))))) = fun z => c * trF τ a b m (M i) (N i) z := by
    intro i
    funext z
    have : (m : ℂ) * ((m : ℂ) ^ 2)⁻¹ = (m : ℂ)⁻¹ := by field_simp
    rw [smul_add, smul_smul, this, trF]
    ring
  refine ⟨th, hth, U, t, i₀, fun j => ((m ^ 2 : ℕ) : ℂ) * fderiv ℂ (u.fr i₀) 0 (W j) / u.fr i₀ 0 - e j,
    fun i => ⟨hUs i, α, s₁, hα, hcorr, htw, hta i⟩, ?_, fun i j => ?_⟩
  · simpa using hi₀
  · have hd := differentiable_trF τ a b m (M i) (N i) hθ
    have hf : FnT u (m ^ 2) (t i) fun z => c * trF τ a b m (M i) (N i) z := by
      rw [← hF i]; exact htf i
    have h1 := GlobalTheory.T.sectionValue_tangentLift_eq_firstJet g x.P u (m ^ 2) (t i) _ (x.v (j.cast hg.symm)) (W j) i₀ hf (hd.const_mul c)
      (x.basis.1 _) (hdiff j) hi₀
    have h2 : u.fr i₀ 0 = valR (𝟙 (Sp ℂ)) ((x.P.L.pull (eSec x.P.A)).U fun _ => i₀) (x.rig.s fun _ => i₀).val := by
      refine hrig (fun _ => i₀) ?_
      intro q hq
      exact Set.mem_iInter.2 fun _ => hi₀ hq
    refine h1.trans ?_
    rw [← h2, fderiv_const_mul (hd 0)]
    congr 3
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring

end GlobalTheory.MBLow.Cl
end
end
