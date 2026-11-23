module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PsiScal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetFiltrationSectionCombination
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRootOfKeyFormula
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.EllipsoidStA
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsUniqueSecIsFnAt
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ValRConstHom
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantsJetsChangeSectionBasis
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanThetaTranslatesTorsionEqTopStatement
import Mathlib.Algebra.Order.Star.Int

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearSectionValueAbelianPower

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.SecValLin
open GlobalTheory.SecJet.Orders

theorem valR_add' {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens) (f g : Γ(X, U)) :
    valR x U (f + g) = valR x U f + valR x U g := by
  by_cases h : ⊤ ≤ x ⁻¹ᵁ U
  · rw [valR_eq x U h, valR_eq x U h, valR_eq x U h, map_add (f := _)]
  · simp only [valR, dif_neg h, add_zero]

theorem valR_scal_mul {R A : Type} [CommRing R] [CommRing A] {X : Scheme.{0}} (ψ : R →+* A) (p : X ⟶ Sp R)
    (x : Sp A ⟶ X) (hx : x ≫ p = spMap ψ) (U : X.Opens) (c : R) (f : Γ(X, U)) :
    valR x U (resTop U (scal p c) * f) = ψ c * valR x U f := by
  by_cases h : ⊤ ≤ x ⁻¹ᵁ U
  · rw [valR_eq x U h, valR_eq x U h, map_mul]
    have e : resTop U (scal p c) = Geo.Tor.constFn p U c := rfl
    rw [e, vh_const ψ p x hx U h c]
  · simp only [valR, dif_neg h, mul_zero]

theorem exists_linear_valR_sec : ∀ (K : Type) [Field K] (x : KeyIn K) (N : ℕ) (i : Fin 1 → x.P.L.ι) (B : Type) [CommRing B] [Algebra K B]
    (y : Sp B ⟶ (baseOver (Sp K) ⊗ x.P.A).left),
    y ≫ (fst (baseOver (Sp K)) x.P.A).left = spMap (algebraMap K B) →
    ∃ f : EA x.P (𝟙 (Sp K)) N →ₗ[K] B, ∀ s : EA x.P (𝟙 (Sp K)) N,
      f s = valR y ((LPow x.P.A x.P.L ((N : ℕ) : ℤ) (baseOver (Sp K))).U i) (s.sec.f i) := by
  intro K _ x N i B _ _ y hy
  refine ⟨⟨⟨fun s => valR y ((LPow x.P.A x.P.L ((N : ℕ) : ℤ) (baseOver (Sp K))).U i) (s.sec.f i),
    fun s t => valR_add' y _ _ _⟩, fun c s => ?_⟩, fun s => rfl⟩
  show valR y _ (resTop _ (scal _ c) * s.sec.f i) = _
  rw [valR_scal_mul (algebraMap K B) _ y hy, RingHom.id_apply, Algebra.smul_def]

end GlobalTheory.SecValLin
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearSectionValueAbelianPowerStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

theorem _root_.GlobalTheory.T.exists_linear_sectionValue_abelianPower : ∀ (K : Type) [Field K] (x : KeyIn K) (N : ℕ) (i : Fin 1 → x.P.L.ι) (B : Type) [CommRing B] [Algebra K B]
    (y : Sp B ⟶ (baseOver (Sp K) ⊗ x.P.A).left),
    y ≫ (fst (baseOver (Sp K)) x.P.A).left = spMap (algebraMap K B) →
    ∃ f : EA x.P (𝟙 (Sp K)) N →ₗ[K] B, ∀ s : EA x.P (𝟙 (Sp K)) N,
      f s = valR y ((LPow x.P.A x.P.L ((N : ℕ) : ℤ) (baseOver (Sp K))).U i) (s.sec.f i) := by
  first | exact @GlobalTheory.SecValLin.exists_linear_valR_sec | exact GlobalTheory.SecValLin.exists_linear_valR_sec | (intros; apply GlobalTheory.SecValLin.exists_linear_valR_sec <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsLineBundlePowSeparateFirstJetsOrigin

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section

namespace GlobalTheory.MBLow.JetSep

theorem sep : ∀ (K : Type) [Field K] (x : KeyIn K) (g : ℕ) (hg : x.P.g = g) (N : ℕ), 4 ≤ N → ∀ (i₀ : x.P.L.ι),
    ⊤ ≤ (𝟙 (Sp K) ≫ eSec x.P.A) ⁻¹ᵁ x.P.L.U i₀ → ∀ (j₀ : Fin g) (a : K) (c : Fin g → K),
    (∀ s : LB.Sec (LPow x.P.A x.P.L (N : ℤ) (baseOver (Sp K))),
      a * (valR (epsLift (x.v (j₀.cast hg.symm))) ((LPow x.P.A x.P.L (N : ℤ) (baseOver (Sp K))).U fun _ => i₀)
          (s.f fun _ => i₀)).fst +
        ∑ j, c j * (valR (epsLift (x.v (j.cast hg.symm))) ((LPow x.P.A x.P.L (N : ℤ) (baseOver (Sp K))).U fun _ => i₀)
          (s.f fun _ => i₀)).snd = 0) →
    a = 0 ∧ c = 0 := by
  intro K _ x g hg N hN i₀ hi₀ j₀ a c H
  subst hg
  have := x.P.isAb.comm
  have k₀ : ⊤ ≤ eSec x.P.A ⁻¹ᵁ x.P.L.U i₀ := by simpa using hi₀
  let U' : x.P.A.left.Opens := (lbPow x.P.L N).U fun _ => i₀
  have hU' : ⊤ ≤ eSec x.P.A ⁻¹ᵁ U' :=
    (GlobalTheory.ThetaFn.le_wchart_unique x.P.L (K := PUnit) (eSec x.P.A) (𝟙 _) (fun _ => i₀)).2 (by simpa using k₀)
  let pb : (lbPow x.P.L N).Sec → LB.Sec (LPow x.P.A x.P.L (N : ℤ) (baseOver (Sp K))) := fun s =>
    GlobalTheory.ThetaFn.pullPow x.P.L (K := PUnit) (K' := Fin 1) (snd (baseOver (Sp K)) x.P.A).left
      (Category.comp_id _) (N : ℤ) s
  have hval : ∀ (s : (lbPow x.P.L N).Sec) (w : epsR K ⟶ x.P.A), IsTangent w →
      valR (epsLift w) ((LPow x.P.A x.P.L (N : ℤ) (baseOver (Sp K))).U fun _ => i₀) ((pb s).f fun _ => i₀) =
        valR w.left U' (s.f fun _ => i₀) := by
    intro s w hw
    have h1 : ⊤ ≤ epsLift w ⁻¹ᵁ ((LPow x.P.A x.P.L (N : ℤ) (baseOver (Sp K))).U fun _ => i₀) := by
      refine (GlobalTheory.ThetaFn.le_wchart_unique x.P.L (K := Fin 1) (epsLift w) _ (fun _ => i₀)).2 ?_
      rw [JetUniq.epsLift_snd]
      exact JetUniq.tan_le hw k₀
    refine (GlobalTheory.HolHom.valR_appLE _ _ _ _ _ _ h1).trans ?_
    rw [JetUniq.epsLift_snd]
    rfl
  have Hs : ∀ s : (lbPow x.P.L N).Sec, a * valR (eSec x.P.A) U' (s.f fun _ => i₀) +
      (valR (tanComb c x.v).left U' (s.f fun _ => i₀)).snd = 0 := by
    intro s
    have e := H (pb s)
    simp only [Fin.cast_eq_self] at e
    rw [hval s _ (x.basis.1 j₀), JetUniq.fst_valR (x.basis.1 j₀) hU'] at e
    rw [JetUniq.snd_valR x.basis.1 (isLieComb_tanComb c x.v) hU']
    refine Eq.trans ?_ e
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hval s _ (x.basis.1 j)]
  obtain ⟨M, sec, hsec⟩ := GlobalTheory.ZH.CrdMove.immBy_lbPow GlobalTheory.allSixLaws.1.ample K x.P N hN
  have key : ∀ d : Fin x.P.g → K, d ≠ 0 → ∃ s₀ s₁ : (lbPow x.P.L N).Sec,
      valR (eSec x.P.A) U' (s₀.f fun _ => i₀) ≠ 0 ∧ valR (eSec x.P.A) U' (s₁.f fun _ => i₀) = 0 ∧
      (valR (tanComb d x.v).left U' (s₁.f fun _ => i₀)).snd ≠ 0 := by
    intro d hd
    have hy := isTangent_tanComb K x.P.A _ x.v d x.basis.1
    obtain ⟨s₀, s₁, h0, h1, h2⟩ := Orders.exists_sep sec hsec hy (Orders.tanComb_ne_one x.basis hd) (fun _ => i₀) hU'
    refine ⟨s₀, s₁, ?_, ?_, ?_⟩
    · rwa [Orders.valR_eq _ _ hU']
    · rwa [Orders.valR_eq _ _ hU']
    · rwa [Orders.valR_eq _ _ (Orders.top_le_tangent hy hU')]
  have hc : c = 0 := by
    by_contra hc
    obtain ⟨-, s₁, -, h1, h2⟩ := key c hc
    have e := Hs s₁
    rw [h1, mul_zero, zero_add] at e
    exact h2 e
  refine ⟨?_, hc⟩
  have hd : (Pi.single j₀ 1 : Fin x.P.g → K) ≠ 0 := fun h => by simpa using congrFun h j₀
  obtain ⟨s₀, -, h0, -, -⟩ := key _ hd
  have e := Hs s₀
  subst hc
  rw [JetUniq.snd_valR x.basis.1 (isLieComb_tanComb 0 x.v) hU'] at e
  simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero] at e
  exact (mul_eq_zero.1 e).resolve_right h0

end GlobalTheory.MBLow.JetSep

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsLineBundlePowSeparateFirstJetsOriginStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

theorem _root_.GlobalTheory.T.sections_lineBundlePow_separate_firstJets_origin : ∀ (K : Type) [Field K] (x : KeyIn K) (g : ℕ) (hg : x.P.g = g) (N : ℕ), 4 ≤ N → ∀ (i₀ : x.P.L.ι),
    ⊤ ≤ (𝟙 (Sp K) ≫ eSec x.P.A) ⁻¹ᵁ x.P.L.U i₀ → ∀ (j₀ : Fin g) (a : K) (c : Fin g → K),
    (∀ s : LB.Sec (LPow x.P.A x.P.L (N : ℤ) (baseOver (Sp K))),
      a * (valR (epsLift (x.v (j₀.cast hg.symm))) ((LPow x.P.A x.P.L (N : ℤ) (baseOver (Sp K))).U fun _ => i₀)
          (s.f fun _ => i₀)).fst +
        ∑ j, c j * (valR (epsLift (x.v (j.cast hg.symm))) ((LPow x.P.A x.P.L (N : ℤ) (baseOver (Sp K))).U fun _ => i₀)
          (s.f fun _ => i₀)).snd = 0) →
    a = 0 ∧ c = 0 := by
  first | exact @GlobalTheory.MBLow.JetSep.sep | exact GlobalTheory.MBLow.JetSep.sep | (intros; apply GlobalTheory.MBLow.JetSep.sep <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantsFirstJetsLinearIndependent

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.MBLow.TRank

theorem main : ∀ (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (x : KeyIn K) (g : ℕ) (hg : x.P.g = g) (m : ℕ), Odd m → 3 ≤ m → ∀ (I : Type) (pt : I → (baseOver (Sp K) ⟶ x.P.A)), (∀ z : baseOver (Sp K) ⟶ x.P.A, z ^ (m ^ 2) = 1 → ∃ i, pt i = z) → ∀ ϑ J, ThJet x hg m pt ϑ J → ∀ (c₀ : K) (c : Fin g → K), (∀ i, c₀ * ϑ i + ∑ j, c j * J i j = 0) → c₀ = 0 ∧ c = 0 := by
  intro K _ _ _ x g hg m hm hm3 I pt hpt ϑ J hTJ c₀ c hrel
  obtain ⟨th, hth, U, t, i₀, c', hUt, hi₀, hval⟩ := hTJ
  have hg1 : 1 ≤ g := hg ▸ x.g_pos
  let j₀ : Fin g := ⟨0, hg1⟩
  have hy : ∀ j : Fin g, epsLift (x.v (j.cast hg.symm)) ≫ (fst (baseOver (Sp K)) x.P.A).left =
      spMap (algebraMap K (DualNumber K)) := fun j => by
    rw [epsLift, ← Over.comp_left, lift_fst]; rfl
  choose f hf using fun j : Fin g => GlobalTheory.T.exists_linear_sectionValue_abelianPower K x (m ^ 2) (fun _ => i₀) (DualNumber K) _ (hy j)
  set a := c₀ - ∑ j, c j * c' j with ha
  let Φ : EA x.P (𝟙 (Sp K)) (m ^ 2) →ₗ[K] K :=
    a • ((TrivSqZeroExt.fstHom K K K).toLinearMap ∘ₗ f j₀) + ∑ j, c j • (TrivSqZeroExt.sndHom K K ∘ₗ f j)
  have hΦ : ∀ s, Φ s = a * (f j₀ s).fst + ∑ j, c j * (f j s).snd := fun s => by
    rw [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sum_apply]
    simp only [LinearMap.smul_apply, LinearMap.comp_apply, smul_eq_mul]
    rfl
  have hft : ∀ j i, f j (SecMod.mk (fst (baseOver (Sp K)) x.P.A).left (t i)) =
      valR (epsLift (x.v (j.cast hg.symm))) ((LPow x.P.A x.P.L ((m ^ 2 : ℕ) : ℤ) (baseOver (Sp K))).U fun _ => i₀)
        ((t i).f fun _ => i₀) := fun j i => hf j _
  have hΦt : ∀ i, Φ (SecMod.mk (fst (baseOver (Sp K)) x.P.A).left (t i)) = 0 := fun i => by
    rw [hΦ]
    simp only [hft, hval]
    set r := valR (𝟙 (Sp K)) ((x.P.L.pull (eSec x.P.A)).U fun _ => i₀) (x.rig.s fun _ => i₀).val ^ (m ^ 2)
    simp only [TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl,
      TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add, TrivSqZeroExt.fst_inr, TrivSqZeroExt.snd_inr, smul_eq_mul,
      MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, add_zero, zero_add, mul_zero, zero_mul]
    have e1 : ∑ j, c j * (r * (J i j + c' j * ϑ i)) = r * ∑ j, c j * J i j + r * ϑ i * ∑ j, c j * c' j := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [e1, ha]
    linear_combination r * hrel i
  have hspan := GlobalTheory.T.span_thetaTranslates_torsion_eq_top K x m hm hm3 I pt hpt th hth U t hUt
  have hΦ0 : Φ = 0 := LinearMap.ext_on_range hspan fun i => by rw [hΦt i, LinearMap.zero_apply]
  have hsep := GlobalTheory.T.sections_lineBundlePow_separate_firstJets_origin K x g hg (m ^ 2) (by nlinarith) i₀ hi₀ j₀ a c fun s => by
    have h := congrArg (fun F => F (SecMod.mk (fst (baseOver (Sp K)) x.P.A).left s)) hΦ0
    simp only [LinearMap.zero_apply, hΦ] at h
    rw [hf j₀, Finset.sum_congr rfl fun j _ => by rw [hf j]] at h
    exact h
  obtain ⟨h1, h2⟩ := hsep
  refine ⟨?_, h2⟩
  subst h2
  simpa [ha] using h1

end GlobalTheory.MBLow.TRank
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantsFirstJetsLinearIndependentStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.thetaConstants_firstJets_linearIndependent : ∀ (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (x : KeyIn K) (g : ℕ) (hg : x.P.g = g) (m : ℕ), Odd m → 3 ≤ m → ∀ (I : Type) (pt : I → (baseOver (Sp K) ⟶ x.P.A)), (∀ z : baseOver (Sp K) ⟶ x.P.A, z ^ (m ^ 2) = 1 → ∃ i, pt i = z) → ∀ ϑ J, ThJet x hg m pt ϑ J → ∀ (c₀ : K) (c : Fin g → K), (∀ i, c₀ * ϑ i + ∑ j, c j * J i j = 0) → c₀ = 0 ∧ c = 0 := by
  first | exact @GlobalTheory.MBLow.TRank.main | exact GlobalTheory.MBLow.TRank.main | (intros; apply GlobalTheory.MBLow.TRank.main <;> assumption)
end
end
