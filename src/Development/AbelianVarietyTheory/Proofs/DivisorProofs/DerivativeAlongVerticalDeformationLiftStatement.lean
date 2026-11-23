module

public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyCuspFrame
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
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueFrameChangeByMatrices
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LowerTriIsUnitDet
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SndEvalPtDir

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.TangentOrigin
open GlobalTheory.FlagMod
open GlobalTheory.FlagTan (dimFlag)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompHS

theorem primeSpectrum_trivSqZeroExt_eq {L M : Type} [Field L] [AddCommGroup M] [Module L M] [Module Lᵐᵒᵖ M]
    [IsCentralScalar L M] (x y : PrimeSpectrum (TrivSqZeroExt L M)) : x = y := by
  have h : ∀ z : PrimeSpectrum (TrivSqZeroExt L M), ∀ a, a ∈ z.asIdeal ↔ a.fst = 0 := fun z a => by
    constructor
    · intro ha
      by_contra h0
      exact z.2.ne_top (z.asIdeal.eq_top_of_isUnit_mem ha (TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (Ne.isUnit h0)))
    · intro ha
      refine z.2.mem_of_pow_mem 2 ?_
      rw [show a ^ 2 = 0 by ext <;> simp [pow_two, ha]]
      exact z.asIdeal.zero_mem
  ext a
  rw [h, h]

theorem le_preimage_of_reduction {R L : Type} [CommRing R] [Field L] (hR : ∀ a b : PrimeSpectrum R, a = b)
    (φ : R →+* L) {T : Scheme.{0}} (x : Sp R ⟶ T) (V : T.Opens) (h : ⊤ ≤ (spMap φ ≫ x) ⁻¹ᵁ V) : ⊤ ≤ x ⁻¹ᵁ V := by
  intro s _
  have hp : (spMap φ) (IsLocalRing.closedPoint L) = s := hR _ _
  have h₁ : (spMap φ ≫ x) (IsLocalRing.closedPoint L) ∈ V := h (Set.mem_univ _)
  exact hp ▸ h₁

theorem le_preimage_of_comp {R S : Type} [CommRing R] [CommRing S] (hR : ∀ a b : PrimeSpectrum R, a = b)
    (φ : R →+* S) (s₀ : Sp S) {T : Scheme.{0}} (x : Sp R ⟶ T) (V : T.Opens) (h : ⊤ ≤ (spMap φ ≫ x) ⁻¹ᵁ V) :
    ⊤ ≤ x ⁻¹ᵁ V := by
  intro s _
  have hp : (spMap φ) s₀ = s := hR _ _
  have h₁ : (spMap φ ≫ x) s₀ ∈ V := h (Set.mem_univ _)
  exact hp ▸ h₁

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : GlobalTheory.FlagMod.FlagCover Y} {Z : Comp Xo c}

theorem exists_thickLift (M : Modif (str₀ X Z) (U₀ X Z) (dimFlag Dw)) {K : Type} [Field K] [Algebra c.F K]
    {ι : Type} [Fintype ι] (z : Sp K ⟶ M.X) (ho : ⊤ ≤ z ⁻¹ᵁ M.off) {Q : FrPt Xo c K} (hz : z ≫ toFlag M = X.ptY Q)
    {W : FrPt Xo c (TrivSqZeroExt K (ι → K))} (hW : FrMap (TrivSqZeroExt.fstHom c.F K (ι → K)) W Q) :
    ∃ ZW : Sp (TrivSqZeroExt K (ι → K)) ⟶ M.X, ZW ≫ toFlag M = X.ptY W ∧
      ∀ (m : ι → K) (x : Sp (DualNumber K) ⟶ M.X),
        x ≫ toFlag M = spMap (GlobalTheory.FlagTan.dir c m).toRingHom ≫ X.ptY W →
          x = spMap (GlobalTheory.FlagTan.dir c m).toRingHom ≫ ZW := by
  have hred : spMap (TrivSqZeroExt.fstHom c.F K (ι → K)).toRingHom ≫ X.ptY W = X.ptY Q := X.ptY_frMap hW
  have hpt : ∀ a b : PrimeSpectrum (TrivSqZeroExt K (ι → K)), a = b := primeSpectrum_trivSqZeroExt_eq
  have hU : ⊤ ≤ (z ≫ M.σ) ⁻¹ᵁ U₀ X Z := fun s _ => by
    have := ho (Set.mem_univ s)
    rw [M.off_eq] at this
    exact this
  have hb : ⊤ ≤ X.ptY W ⁻¹ᵁ (inc₀ X Z).opensRange :=
    le_preimage_of_reduction hpt (TrivSqZeroExt.fstHom c.F K (ι → K)).toRingHom _ _ (by
      rw [hred, ← hz]
      rintro s -
      exact ⟨(z ≫ M.σ) s, rfl⟩)
  have hr : Set.range (X.ptY W) ⊆ Set.range (inc₀ X Z) := by
    rintro _ ⟨s, rfl⟩
    exact hb (Set.mem_univ s)
  obtain ⟨w₁, hw₁⟩ : ∃ w₁, w₁ ≫ inc₀ X Z = X.ptY W := ⟨_, IsOpenImmersion.lift_fac _ _ hr⟩
  have ered : spMap (TrivSqZeroExt.fstHom c.F K (ι → K)).toRingHom ≫ w₁ = z ≫ M.σ := by
    rw [← cancel_mono (inc₀ X Z), Category.assoc, hw₁, hred, ← hz, Category.assoc]
  have hwU : ⊤ ≤ w₁ ⁻¹ᵁ U₀ X Z := le_preimage_of_reduction hpt _ _ _ (by rw [ered]; exact hU)
  obtain ⟨ZW, hZW, -⟩ := M.existsUnique_lift w₁ hwU
  refine ⟨ZW, by rw [toFlag, ← Category.assoc, hZW, hw₁], fun m x hx => ?_⟩
  have hxU : ⊤ ≤ (spMap (GlobalTheory.FlagTan.dir c m).toRingHom ≫ w₁) ⁻¹ᵁ U₀ X Z := fun s _ => hwU (Set.mem_univ _)
  refine (M.existsUnique_lift _ hxU).unique ?_ (by rw [Category.assoc, hZW])
  rw [← cancel_mono (inc₀ X Z), Category.assoc, Category.assoc, hw₁, ← hx]

theorem snd_evalPt_dir {K : Type} [Field K] [Algebra c.F K] {ι : Type} [Fintype ι] {T : Scheme.{0}}
    (ZW : Sp (TrivSqZeroExt K (ι → K)) ⟶ T) (O : T.Opens) (hO : ⊤ ≤ ZW ⁻¹ᵁ O) (m : ι → K)
    (x : Sp (DualNumber K) ⟶ T) (hx : ⊤ ≤ x ⁻¹ᵁ O) (e : x = spMap (GlobalTheory.FlagTan.dir c m).toRingHom ≫ ZW) (g : Γ(T, O)) :
    (evalPt x O hx g).snd = ∑ k, (evalPt ZW O hO g).snd k * m k := by
  subst e
  rw [evalPt_spMap_comp (GlobalTheory.FlagTan.dir c m).toRingHom ZW O hO hx g]
  exact GlobalTheory.FlagTan.snd_dir m _

end GlobalTheory.CompHS
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivativeAlongVerticalDeformationLift

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.TangentOrigin
open GlobalTheory.FlagMod GlobalTheory.TopForm
open GlobalTheory.FlagTan (dimFlag psiSet TIx HIx VIx IsTanFrame IsDef IsVert KSIso kap)
open GlobalTheory.AllWt (exOf)
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompHS

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : GlobalTheory.FlagMod.FlagCover Y} {Z : Comp Xo c}


open GlobalTheory.FlagTan in
theorem der_fun_ver (M : Modif (str₀ X Z) (U₀ X Z) (dimFlag Dw)) {K : Type} [Field K] [Algebra c.F K]
    (z : Sp K ⟶ M.X) (ho : ⊤ ≤ z ⁻¹ᵁ M.off)
    {Q : FrPt Xo c K} (hz : z ≫ toFlag M = X.ptY Q)
    {v : VIx Dw → FrPt Xo c (DualNumber K)} (hv : ∀ k : VIx Dw, IsVert Q (Pi.single k.toF (1 : K)) (v k))
    {zv : VIx Dw → (Sp (DualNumber K) ⟶ M.X)} (hl : ∀ b, zv b ≫ toFlag M = X.ptY (v b))
    {w : FrPt Xo c (DualNumber K)} {N : FIx Dw → K} (hw : IsVert Q N w)
    {zw : Sp (DualNumber K) ⟶ M.X} (hlw : zw ≫ toFlag M = X.ptY w)
    (O : M.X.Opens) (g : Γ(M.X, O)) (hzw : ⊤ ≤ zw ⁻¹ᵁ O) (hzv : ∀ b, ⊤ ≤ zv b ⁻¹ᵁ O) :
    (evalPt zw O hzw g).snd = ∑ k : VIx Dw, N k.toF * (evalPt (zv k) O (hzv _) g).snd := by
  choose vp hvp using fun m : FIx Dw → K => (existsUnique_isVert Q m).exists
  obtain ⟨y₀, h₀⟩ := GlobalTheory.FlagTan.exists_frMap (cst c K) Q
  obtain ⟨W₀, hW₀⟩ := GlobalTheory.FlagTan.exists_frMap (TrivSqZeroExt.inlAlgHom c.F K (FIx Dw → K)) Q
  let n : FIx Dw → FIx Dw → K := fun k => Pi.single k 1
  obtain ⟨W, hW, -⟩ :=
    GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c _ W₀ _ (isUnit_unip₀ (K := K) n).unit (isUnit_det_unip n)

  have hWm : ∀ m, FrMap (dir c m) W (vp m) := fun m => by
    obtain ⟨y₁, h₁, hs⟩ := hvp m
    obtain rfl := GlobalTheory.FlagTan.frMap_unique h₁ h₀
    refine (GlobalTheory.FlagTan.frMap_iff_frChg hW (GlobalTheory.FlagTan.frMap_of_comp hW₀ h₀ fun a => by ext <;> simp)).2 ?_
    unfold IsShift at hs
    convert hs using 2 with τ
    · ext i j <;> simp [unip, n, Pi.single_apply]
    · ext <;> simp [unip₀, n, Pi.single_apply]
  have hP : ∀ m, spMap (dir c m).toRingHom ≫ X.ptY W = X.ptY (vp m) := fun m => X.ptY_frMap (hWm m)
  obtain ⟨ZW, hZf, huniq⟩ := exists_thickLift M z ho hz
    (GlobalTheory.FlagTan.frMap_comp (hWm 0) (hvp 0).isDef fun a => by simp)
  have huniq' : ∀ m (x : Sp (DualNumber K) ⟶ M.X), x ≫ toFlag M = X.ptY (vp m) →
      x = spMap (dir c m).toRingHom ≫ ZW := fun m x hx => huniq m x (hx.trans (hP m).symm)
  have ew : zw = spMap (dir c N).toRingHom ≫ ZW :=
    huniq' N zw (by rw [hlw, (existsUnique_isVert Q N).unique hw (hvp N)])
  have hZO : ⊤ ≤ ZW ⁻¹ᵁ O :=
    le_preimage_of_comp primeSpectrum_trivSqZeroExt_eq (dir c N).toRingHom
      ((spMap (red c K).toRingHom) (IsLocalRing.closedPoint K)) ZW O (ew ▸ hzw)

  have hflag : ∀ N' : FIx Dw → K, (∀ σ i j, i < j → N' (some ⟨σ, i, j⟩) = 0) → X.ptY (vp N') = X.ptY y₀ :=
    fun N' hN' => by
      obtain ⟨y₁, h₁, hs⟩ := hvp N'
      obtain rfl := GlobalTheory.FlagTan.frMap_unique h₁ h₀
      exact (X.ptY_frBor (t := fun k => oneAddEps (Multiplicative.ofAdd (diagOf N' k)))
        ((GlobalTheory.Frames.frBor_iff_frChg _ _ _).2 ⟨unip K N', fun σ i j hij => by
          simp [unip, hN' σ i j hij, hij.ne], fun _ _ => by simp [unip, oneAddEps, diagOf], hs⟩)).symm
  have h0 : ∀ j : FIx Dw, j ∉ Set.range VIx.toF → (evalPt ZW O hZO g).snd j = 0 := fun j hj => by
    have hx : ⊤ ≤ (spMap (dir c (Pi.single j 1)).toRingHom ≫ ZW) ⁻¹ᵁ O := fun s _ => hZO (Set.mem_univ _)
    have e1 := huniq 0 (spMap (dir c (Pi.single j 1)).toRingHom ≫ ZW) (by
      rw [Category.assoc, hZf, hP, hP, hflag _ (fun σ i j' hij => Pi.single_eq_of_ne (by
        rintro rfl
        exact hj ⟨⟨σ, (i, j'), hij⟩, rfl⟩) _), hflag 0 fun _ _ _ _ => rfl])
    have a1 := snd_evalPt_dir ZW O hZO (Pi.single j 1) _ hx rfl g
    have a2 := snd_evalPt_dir ZW O hZO 0 _ hx e1 g
    simpa [Pi.single_apply] using a1.symm.trans a2
  have hk : ∀ k : VIx Dw, (evalPt (zv k) O (hzv k) g).snd = (evalPt ZW O hZO g).snd k.toF := fun k => by
    rw [snd_evalPt_dir ZW O hZO _ _ _
      (huniq' _ _ ((hl k).trans (congrArg X.ptY ((existsUnique_isVert Q _).unique (hv k) (hvp _))))) g]
    simp [Pi.single_apply]
  rw [snd_evalPt_dir ZW O hZO N zw hzw ew g]
  simp only [hk]
  have hz0 : ∑ k ∈ Finset.univ.filter (fun k => k ∉ Set.range VIx.toF), (evalPt ZW O hZO g).snd k * N k = 0 :=
    Finset.sum_eq_zero fun k hk => by rw [h0 k (Finset.mem_filter.1 hk).2, zero_mul]
  rw [sum_FIx, hz0, add_zero]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

end GlobalTheory.CompHS
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivativeAlongVerticalDeformationLiftStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.TangentOrigin
open GlobalTheory.FlagMod GlobalTheory.TopForm
open GlobalTheory.FlagTan (dimFlag psiSet TIx HIx VIx IsTanFrame IsDef IsVert KSIso kap)
open GlobalTheory.AllWt (exOf)
open scoped Classical

theorem _root_.GlobalTheory.T.derivative_along_vertical_deformation_lift : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : GlobalTheory.FlagMod.FlagCover Y} {Z : Comp Xo c} (M : Modif (str₀ X Z) (U₀ X Z) (GlobalTheory.FlagTan.dimFlag Dw)) {K : Type} [Field K] [Algebra c.F K] (z : Sp K ⟶ M.X) (ho : ⊤ ≤ z ⁻¹ᵁ M.off)
    {Q : FrPt Xo c K} (hz : z ≫ toFlag M = X.ptY Q)
    {v : VIx Dw → FrPt Xo c (DualNumber K)} (hv : ∀ k : VIx Dw, IsVert Q (Pi.single k.toF (1 : K)) (v k))
    {zv : VIx Dw → (Sp (DualNumber K) ⟶ M.X)} (hl : ∀ b, zv b ≫ toFlag M = X.ptY (v b))
    {w : FrPt Xo c (DualNumber K)} {N : GlobalTheory.FlagTan.FIx Dw → K} (hw : IsVert Q N w)
    {zw : Sp (DualNumber K) ⟶ M.X} (hlw : zw ≫ toFlag M = X.ptY w)
    (O : M.X.Opens) (g : Γ(M.X, O)) (hzw : ⊤ ≤ zw ⁻¹ᵁ O) (hzv : ∀ b, ⊤ ≤ zv b ⁻¹ᵁ O), (evalPt zw O hzw g).snd = ∑ k : VIx Dw, N k.toF * (evalPt (zv k) O (hzv _) g).snd := by
  first | exact @GlobalTheory.CompHS.der_fun_ver | exact GlobalTheory.CompHS.der_fun_ver | (intros; apply GlobalTheory.CompHS.der_fun_ver <;> assumption)
end
end
