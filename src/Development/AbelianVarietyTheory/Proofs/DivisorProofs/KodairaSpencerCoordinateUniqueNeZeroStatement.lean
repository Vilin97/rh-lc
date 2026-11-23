module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsKSIffKsRel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroTangentOfJacobianDerivsVanishStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitMkOfFormallyUnramified
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AbelianVarietyTheory.Definitions.Divisors.CommGroupMulMulEqMulInvMulMulMul
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsChartOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnitaryWeightExponentVectorSignatureWeightMuZero
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyCuspFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniversalFirstOrderDeformationStatement
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.FrameBorelGroupoidProperties
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsJacobianEvalRingPointNeZero

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.TangentOrigin GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag psiSet TIx IsTanFrame)
open scoped Classical

namespace GlobalTheory


open GlobalTheory.TopForm in
theorem CanonLB.exists_jacobian_evalPt_ne_zero : ∀ {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {D : ℕ} [SmoothOfRelativeDimension D p] (K : GlobalTheory.CanonLB p D) (i : K.bundle.ι) {F : Type} [Field F] (z : Sp F ⟶ Y) (hz : ⊤ ≤ z ⁻¹ᵁ K.bundle.U i), ∃ g : Fin D → Γ(Y, K.bundle.U i), evalPt z _ hz (K.jacobian i le_rfl g) ≠ 0 := by
  intro k _ Y p D _ K i F _ z hz
  by_contra hcon
  push_neg at hcon
  let Sm : Submodule Γ(Y, K.bundle.U i) (FormsOn p D (K.bundle.U i)) :=
    Submodule.comap (K.coeff i le_rfl) (RingHom.ker (evalPt z _ hz))
  have hsub : Set.range (dForm (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p (K.bundle.U i)) (D := D)) ⊆ (Sm : Set _) := by
    rintro _ ⟨g, rfl⟩
    exact (RingHom.mem_ker).2 (hcon g)
  have hle : (⊤ : Submodule Γ(Y, K.bundle.U i) (FormsOn p D (K.bundle.U i))) ≤ Sm := by
    rw [← span_dForm (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p (K.bundle.U i)) D]
    exact Submodule.span_le.2 hsub
  have hmem : resForm (le_rfl : K.bundle.U i ≤ K.bundle.U i) (K.om i) ∈ Sm := hle Submodule.mem_top
  have h1 : evalPt z _ hz (K.coeff i le_rfl (resForm le_rfl (K.om i))) = 0 :=
    (RingHom.mem_ker).1 hmem
  rw [K.coeff_om, map_one] at h1
  exact one_ne_zero h1

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsJacobianEvalRingPointNeZeroStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.TangentOrigin GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag psiSet TIx IsTanFrame)
open scoped Classical

theorem _root_.GlobalTheory.T.exists_jacobian_evalRingPoint_ne_zero : ∀ {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {D : ℕ} [SmoothOfRelativeDimension D p] (K : GlobalTheory.CanonLB p D) (i : K.bundle.ι) {F : Type} [Field F] (z : Sp F ⟶ Y) (hz : ⊤ ≤ z ⁻¹ᵁ K.bundle.U i), ∃ g : Fin D → Γ(Y, K.bundle.U i), evalPt z _ hz (K.jacobian i le_rfl g) ≠ 0 := by
  first | exact @GlobalTheory.CanonLB.exists_jacobian_evalPt_ne_zero | exact GlobalTheory.CanonLB.exists_jacobian_evalPt_ne_zero | (intros; apply GlobalTheory.CanonLB.exists_jacobian_evalPt_ne_zero <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueModificationLiftSqZeroFlag

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.TangentOrigin GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag psiSet TIx IsTanFrame)
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ModifLift

theorem spMap_fst_surjective_sqZero (K : Type) [Field K] (ι : Type) :
    Function.Surjective (spMap (TrivSqZeroExt.fstHom K K (ι → K)).toRingHom) := by
  intro p
  refine ⟨(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K), ?_⟩
  refine PrimeSpectrum.ext (Ideal.ext fun x => ?_)
  change x.fst ∈ (⊥ : Ideal K) ↔ x ∈ PrimeSpectrum.asIdeal p
  rw [Ideal.mem_bot]
  constructor
  · intro hx
    apply p.isPrime.mem_of_pow_mem 2
    have : x ^ 2 = 0 := by
      rw [pow_two, show x = TrivSqZeroExt.inr x.snd from TrivSqZeroExt.ext hx rfl,
        TrivSqZeroExt.inr_mul_inr]
    rw [this]
    exact Ideal.zero_mem _
  · intro hx
    by_contra h0
    have hu : IsUnit x := TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (Ne.isUnit h0)
    exact p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hx hu)

theorem exists_lift_sqZero {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : FlagCover Y} {Z : Comp Xo c}
    (M : Modif (str₀ X Z) (U₀ X Z) (dimFlag Dw)) {K : Type} [Field K] {ι : Type} (z : Sp K ⟶ M.X)
    (hz : ⊤ ≤ z ⁻¹ᵁ M.off) (w : Sp (TrivSqZeroExt K (ι → K)) ⟶ X.YY)
    (hw : spMap (TrivSqZeroExt.fstHom K K (ι → K)).toRingHom ≫ w = z ≫ toFlag M) :
    ∃ w' : Sp (TrivSqZeroExt K (ι → K)) ⟶ M.X, w' ≫ toFlag M = w ∧
      spMap (TrivSqZeroExt.fstHom K K (ι → K)).toRingHom ≫ w' = z ∧
      ∀ O : M.X.Opens, ⊤ ≤ z ⁻¹ᵁ O → ⊤ ≤ w' ⁻¹ᵁ O := by
  set f := spMap (TrivSqZeroExt.fstHom K K (ι → K)).toRingHom with hf
  have hs := spMap_fst_surjective_sqZero K ι
  have hr : Set.range w ⊆ Set.range (inc₀ X Z) := by
    rintro _ ⟨t, rfl⟩
    obtain ⟨s, rfl⟩ := hs t
    refine ⟨M.σ (z s), ?_⟩
    change (z ≫ M.σ ≫ inc₀ X Z) s = (f ≫ w) s
    rw [hw]
  set w₀ := IsOpenImmersion.lift (inc₀ X Z) w hr with hw₀
  have hw₀f : w₀ ≫ inc₀ X Z = w := IsOpenImmersion.lift_fac _ _ _
  have hfw₀ : f ≫ w₀ = z ≫ M.σ := by
    rw [← cancel_mono (inc₀ X Z), Category.assoc, hw₀f, hw, Category.assoc]
  have hzU : ∀ s, M.σ (z s) ∈ U₀ X Z := fun s => by
    have := hz (Set.mem_univ s)
    rw [M.off_eq] at this
    exact this
  have hU : ⊤ ≤ w₀ ⁻¹ᵁ U₀ X Z := by
    intro t _
    obtain ⟨s, rfl⟩ := hs t
    change (f ≫ w₀) s ∈ U₀ X Z
    rw [hfw₀]
    exact hzU s
  obtain ⟨w', hw', -⟩ := M.existsUnique_lift w₀ hU
  have hU' : ⊤ ≤ (f ≫ w₀) ⁻¹ᵁ U₀ X Z := fun s _ => hU (Set.mem_univ (f s))
  have hfw' : f ≫ w' = z := by
    obtain ⟨_, -, huniq⟩ := M.existsUnique_lift (f ≫ w₀) hU'
    exact (huniq _ (show (f ≫ w') ≫ M.σ = f ≫ w₀ by rw [Category.assoc, hw'])).trans (huniq z hfw₀.symm).symm
  refine ⟨w', ?_, hfw', fun O hO t _ => ?_⟩
  · rw [toFlag, ← Category.assoc, hw', hw₀f]
  · obtain ⟨s, rfl⟩ := hs t
    change (f ≫ w') s ∈ O
    rw [hfw']
    exact hO (Set.mem_univ s)

end GlobalTheory.ModifLift
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueModificationLiftSqZeroFlagStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.TangentOrigin GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag psiSet TIx IsTanFrame)
open scoped Classical

theorem _root_.GlobalTheory.T.existsUnique_modification_lift_sqZero_flag : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : FlagCover Y} {Z : Comp Xo c} (M : Modif (str₀ X Z) (U₀ X Z) (dimFlag Dw)) {K : Type} [Field K] {ι : Type} (z : Sp K ⟶ M.X), ⊤ ≤ z ⁻¹ᵁ M.off → ∀ (w : Sp (TrivSqZeroExt K (ι → K)) ⟶ X.YY), spMap (TrivSqZeroExt.fstHom K K (ι → K)).toRingHom ≫ w = z ≫ toFlag M → ∃ w' : Sp (TrivSqZeroExt K (ι → K)) ⟶ M.X, w' ≫ toFlag M = w ∧ spMap (TrivSqZeroExt.fstHom K K (ι → K)).toRingHom ≫ w' = z ∧ ∀ O : M.X.Opens, ⊤ ≤ z ⁻¹ᵁ O → ⊤ ≤ w' ⁻¹ᵁ O := by
  first | exact @GlobalTheory.ModifLift.exists_lift_sqZero | exact GlobalTheory.ModifLift.exists_lift_sqZero | (intros; apply GlobalTheory.ModifLift.exists_lift_sqZero <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerCoordinateUniqueNeZero

section

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompHS

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CechPic GlobalTheory.TangentOrigin GlobalTheory.Vanishing
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag psiSet TIx IsTanFrame)
open GlobalTheory.AllWt (exOf)
open scoped Classical

theorem spectrumMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (a : A →+* B) (b : B →+* C) :
    spMap b ≫ spMap a = spMap (b.comp a) := (Spec.map_comp _ _).symm

theorem exists_datum {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : FlagCover Y} {Z : Comp Xo c}
    (M : Modif (str₀ X Z) (U₀ X Z) (dimFlag Dw))
    (hKS : ∀ (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), GlobalTheory.FlagTan.KSIso (psiSet H) y)
    (i : M.K.bundle.ι) (k : X.F.J) (K : Type) [Field K] (z : Sp K ⟶ M.X) (hz : ⊤ ≤ z ⁻¹ᵁ ksOpen M i k) :
    ∃ (_ : Algebra c.F K) (P Q : FrPt Xo c K) (t : Ix Dw → Kˣ) (v : TIx Dw (psiSet H) → FrPt Xo c (DualNumber K))
      (zv : TIx Dw (psiSet H) → (Sp (DualNumber K) ⟶ M.X)) (O : M.X.Opens) (hO : O ≤ M.K.bundle.U i)
      (g : Fin (dimFlag Dw) → Γ(M.X, O)) (hz : ⊤ ≤ z ⁻¹ᵁ O) (hzv : ∀ b, ⊤ ≤ zv b ⁻¹ᵁ O)
      (hk : ⊤ ≤ (z ≫ toFlag M) ⁻¹ᵁ X.F.U k),
      X.F.ChartFr k (z ≫ toFlag M) hk Q ∧ FrBor t Q P ∧ IsTanFrame (psiSet H) P v ∧
      (∀ b, zv b ≫ toFlag M = X.ptY (v b)) ∧
      (Matrix.of fun a b => (evalPt (zv (tanOrd Dw b)) O (hzv _) (g a)).snd).det ≠ 0 ∧
      (∏ ix, t ix ^ exOf Dw (FlagTan.kap Dw) 0 ix).val * evalPt z O hz (M.K.jacobian i hO g) ≠ 0 := by
  have ho : ⊤ ≤ z ⁻¹ᵁ M.off := fun s hs => (hz hs).1
  have hi : ⊤ ≤ z ⁻¹ᵁ M.K.bundle.U i := fun s hs => (hz hs).2.1
  have hk : ⊤ ≤ (z ≫ toFlag M) ⁻¹ᵁ X.F.U k := fun s hs =>
    (((common₀ X Z).pull M.σ).mem _ k _).1 (hz hs).2.2
  have hfo : ⊤ ≤ (z ≫ toFlag M) ⁻¹ᵁ flagOpen X := fun s hs => by
    have := ho hs
    rw [M.off_eq] at this
    exact this
  obtain ⟨alg, hQex⟩ := exists_chartFr (z ≫ toFlag M) hfo
  obtain ⟨Q, hQ⟩ := hQex k hk
  have hzQ : z ≫ toFlag M = X.ptY Q := FlagCover.eq_ptY hQ.lies
  obtain ⟨W, v, hWP, hWv, hv, hinj⟩ := GlobalTheory.T.exists_universal_first_order_deformation X K Q (hKS K Q)
  have hW0 : spMap (TrivSqZeroExt.fstHom K K (TIx Dw (psiSet H) → K)).toRingHom ≫ X.ptY W = z ≫ toFlag M := by
    have e : (TrivSqZeroExt.fstHom K K (TIx Dw (psiSet H) → K)).toRingHom =
        (TrivSqZeroExt.fstHom c.F K (TIx Dw (psiSet H) → K)).toRingHom := RingHom.ext fun _ => rfl
    rw [hzQ, e]; exact X.ptY_frMap hWP
  obtain ⟨W', hW'1, hW'2, hW'3⟩ := GlobalTheory.T.existsUnique_modification_lift_sqZero_flag M z ho (X.ptY W) hW0
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_jacobian_evalRingPoint_ne_zero M.K i z hi
  have hW'O := hW'3 _ hi
  have hpre : ∀ {R : Type} [CommRing R] (φ : TrivSqZeroExt K (TIx Dw (psiSet H) → K) →+* R),
      ⊤ ≤ (spMap φ ≫ W') ⁻¹ᵁ M.K.bundle.U i := fun φ s _ => hW'O (Set.mem_univ ((spMap φ).base s))
  let zv : TIx Dw (psiSet H) → (Sp (DualNumber K) ⟶ M.X) := fun b =>
    spMap (GlobalTheory.FlagTan.dir c (Pi.single b (1 : K))).toRingHom ≫ W'
  have hzv : ∀ b, ⊤ ≤ zv b ⁻¹ᵁ M.K.bundle.U i := fun b => hpre _
  have hent : ∀ a b, (evalPt (zv b) _ (hzv b) (g a)).snd = (evalPt W' _ hW'O (g a)).snd b := fun a b => by
    simp only [zv]
    rw [evalPt_spMap_comp _ W' _ hW'O]
    simp [Pi.single_apply]
  have hdet : (Matrix.of fun a b => (evalPt (zv (tanOrd Dw b)) _ (hzv _) (g a)).snd).det ≠ 0 := by
    intro hd
    obtain ⟨m, hm0, hm⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hd
    let m' : TIx Dw (psiSet H) → K := fun b => m ((tanOrd Dw).symm b)
    obtain ⟨u, hu⟩ := GlobalTheory.FlagTan.exists_frMap (GlobalTheory.FlagTan.dir c m') W
    obtain ⟨P₀, hP₀⟩ := GlobalTheory.FlagTan.exists_frMap (GlobalTheory.FlagTan.cst c K) Q
    have key := GlobalTheory.T.eq_zero_tangent_of_jacobian_derivs_vanish M.K i z hi g hg (spMap (GlobalTheory.FlagTan.dir c m').toRingHom ≫ W') (hpre _) ?_ ?_ ?_
    · apply hm0
      have hm'0 : m' = 0 := by
        refine hinj m' u P₀ hu hP₀ ?_
        rw [← X.ptY_frMap hu, ← X.ptY_frMap hP₀, ← hW'1, ← hzQ, ← Category.assoc, key, Category.assoc]
        rfl
      funext b
      simpa [m'] using congrFun hm'0 (tanOrd Dw b)
    · rw [← Category.assoc, spectrumMap_comp, ← hW'2]
      congr 2
      ext x <;> simp
    · have a1 : W' ≫ M.σ ≫ inc₀ X Z ≫ flagStr X = spMap (algebraMap c.F _) := by
        rw [← Category.assoc M.σ, ← Category.assoc W']
        exact (congrArg (· ≫ flagStr X) hW'1).trans (ptY_str X W)
      have a2 : z ≫ M.σ ≫ inc₀ X Z ≫ flagStr X = spMap (algebraMap c.F K) := by
        rw [← Category.assoc M.σ, ← Category.assoc z]
        exact (congrArg (· ≫ flagStr X) hzQ).trans (ptY_str X Q)
      change (spMap _ ≫ W') ≫ M.σ ≫ inc₀ X Z ≫ flagStr X = spMap _ ≫ z ≫ M.σ ≫ inc₀ X Z ≫ flagStr X
      rw [Category.assoc, a1, a2, spectrumMap_comp, spectrumMap_comp]
      refine congrArg spMap (RingHom.ext fun x => ?_)
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]
      rfl
    · intro a
      rw [evalPt_spMap_comp _ W' _ hW'O]
      have := congrFun hm a
      simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, hent] at this
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, GlobalTheory.FlagTan.snd_dir]
      rw [← (tanOrd Dw).sum_comp]
      simpa [m'] using this
  refine ⟨alg, Q, Q, 1, v, zv, _, le_rfl, g, hi, hzv, hk, hQ,
    (GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H Dw l Xo c K).1 Q, hv, fun b => ?_, hdet, ?_⟩
  · simp only [zv]
    rw [Category.assoc, hW'1]
    exact X.ptY_frMap (hWv b)
  · simpa using hg

theorem ksRel_unique_ne_zero : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : GlobalTheory.FlagMod.FlagCover Y}
    {Z : Comp Xo c} (M : Modif (str₀ X Z) (U₀ X Z) (GlobalTheory.FlagTan.dimFlag Dw)),
    (∀ (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), GlobalTheory.FlagTan.KSIso (GlobalTheory.FlagTan.psiSet H) y) →
    ∀ (i : M.K.bundle.ι) (k : X.F.J) (K : Type) [Field K] (z : Sp K ⟶ M.X), ⊤ ≤ z ⁻¹ᵁ ksOpen M i k →
      (∀ x y : K, KSRel M i k z x → KSRel M i k z y → x = y) ∧ ∀ x : K, KSRel M i k z x → x ≠ 0 := by
  intro E _ _ _ H Dw l Xo c Y X Z M hKS i k K _ z hz
  obtain ⟨alg, P, Q, t, v, zv, O, hO, g, hz', hzv, hk, hQ, ht, hv, hl, hd, hr⟩ := exists_datum M hKS i k K z hz
  refine ⟨fun x y hx hy => mul_right_cancel₀ hd ((hx P Q t v zv O hO g hz' hzv hk hQ ht hv hl).trans
    (hy P Q t v zv O hO g hz' hzv hk hQ ht hv hl).symm), fun x hx h0 => hr ?_⟩
  have := hx P Q t v zv O hO g hz' hzv hk hQ ht hv hl
  rw [h0, zero_mul] at this
  exact this.symm

end GlobalTheory.CompHS
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerCoordinateUniqueNeZeroStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS

theorem _root_.GlobalTheory.T.kodairaSpencer_coordinate_unique_ne_zero : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : GlobalTheory.FlagMod.FlagCover Y} {Z : Comp Xo c} (M : Modif (str₀ X Z) (U₀ X Z) (GlobalTheory.FlagTan.dimFlag Dw)), (∀ (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), GlobalTheory.FlagTan.KSIso (GlobalTheory.FlagTan.psiSet H) y) → ∀ (i : M.K.bundle.ι) (k : X.F.J) (K : Type) [Field K] (z : Sp K ⟶ M.X), ⊤ ≤ z ⁻¹ᵁ ksOpen M i k → (∀ x y : K, KSRel M i k z x → KSRel M i k z y → x = y) ∧ ∀ x : K, KSRel M i k z x → x ≠ 0 := by
  first | exact @GlobalTheory.CompHS.ksRel_unique_ne_zero | exact GlobalTheory.CompHS.ksRel_unique_ne_zero | (intros; apply GlobalTheory.CompHS.ksRel_unique_ne_zero <;> assumption)
end
end
