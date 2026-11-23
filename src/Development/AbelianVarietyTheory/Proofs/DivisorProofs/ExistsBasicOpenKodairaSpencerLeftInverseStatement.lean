module

public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyCuspFrame
public import Mathlib.AlgebraicGeometry.AffineScheme
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChartFrameDeformationOfDerivationCombinatiStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeSpectrumDualNumberEq
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineOpenExistsFieldPointBasicOpenCommonDenomAl

section

@[expose] public section

open AlgebraicGeometry

namespace GlobalTheory

theorem affineOpen_exists_field_point_basicOpen_commonDenom :
    ∀ {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) (p : X), p ∈ U →
      ∃ (K : Type) (_ : Field K) (ψ : Γ(X, U) →+* K), (∀ g, ψ g ≠ 0 → p ∈ X.basicOpen g) ∧
        ∀ (ι : Type) [Fintype ι] (m : ι → K), ∃ (a : ι → Γ(X, U)) (t : Γ(X, U)),
          ψ t ≠ 0 ∧ ∀ i, m i * ψ t = ψ (a i) := by
  intro X U hU p hp
  classical
  let P := hU.primeIdealOf ⟨p, hp⟩
  haveI : P.asIdeal.IsPrime := P.isPrime
  let K := FractionRing (Γ(X, U) ⧸ P.asIdeal)
  let ψ : Γ(X, U) →+* K := (algebraMap (Γ(X, U) ⧸ P.asIdeal) K).comp (Ideal.Quotient.mk P.asIdeal)
  have hψ : ∀ g, ψ g ≠ 0 ↔ g ∉ P.asIdeal := by
    intro g
    simp only [ψ, RingHom.comp_apply, ne_eq]
    rw [map_eq_zero_iff _ (IsFractionRing.injective _ _), Ideal.Quotient.eq_zero_iff_mem]
  refine ⟨K, inferInstance, ψ, ?_, ?_⟩
  · intro g hg
    have h1 : P ∈ PrimeSpectrum.basicOpen g := (hψ g).1 hg
    rw [← hU.fromSpec_preimage_basicOpen] at h1
    have h2 : hU.fromSpec P = p := hU.fromSpec_primeIdealOf ⟨p, hp⟩
    have h3 : hU.fromSpec P ∈ X.basicOpen g := h1
    rwa [h2] at h3
  · intro ι _ m
    have hrep : ∀ i, ∃ b s : Γ(X, U), ψ s ≠ 0 ∧ m i * ψ s = ψ b := by
      intro i
      obtain ⟨⟨b', ⟨s', hs'⟩⟩, he⟩ := IsLocalization.mk'_surjective
        (nonZeroDivisors (Γ(X, U) ⧸ P.asIdeal)) (m i)
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b'
      obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective s'
      refine ⟨b, s, ?_, ?_⟩
      · simp only [ψ, RingHom.comp_apply, ne_eq]
        exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs'
      · rw [← he]
        simp only [ψ, RingHom.comp_apply]
        exact IsLocalization.mk'_spec _ _ _
    choose b s hs hbs using hrep
    refine ⟨fun i => b i * ∏ j ∈ Finset.univ.erase i, s j, ∏ j, s j, ?_, ?_⟩
    · rw [map_prod]
      exact Finset.prod_ne_zero_iff.2 (fun j _ => hs j)
    · intro i
      rw [map_prod, ← Finset.mul_prod_erase Finset.univ (fun j => ψ (s j)) (Finset.mem_univ i),
        ← mul_assoc, hbs i, map_mul, map_prod]

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineOpenExistsFieldPointBasicOpenCommonDenomAlStatement

section

@[expose] public section

open AlgebraicGeometry

theorem _root_.GlobalTheory.T.exists_ringHom_field_common_denom_of_mem_isAffineOpen : ∀ {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) (p : X), p ∈ U → ∃ (K : Type) (_ : Field K) (ψ : Γ(X, U) →+* K), (∀ g, ψ g ≠ 0 → p ∈ X.basicOpen g) ∧ ∀ (ι : Type) [Fintype ι] (m : ι → K), ∃ (a : ι → Γ(X, U)) (t : Γ(X, U)), ψ t ≠ 0 ∧ ∀ i, m i * ψ t = ψ (a i) := by
  first | exact @GlobalTheory.affineOpen_exists_field_point_basicOpen_commonDenom | exact GlobalTheory.affineOpen_exists_field_point_basicOpen_commonDenom | (intros; apply GlobalTheory.affineOpen_exists_field_point_basicOpen_commonDenom <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenKodairaSpencerLeftInverse

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.TangentOrigin
open GlobalTheory.FlagMod GlobalTheory.TopForm
open GlobalTheory.FlagTan (dimFlag psiSet TIx HIx VIx IsTanFrame IsDef IsVert KSIso kap)
open GlobalTheory.AllWt (exOf)
open scoped Classical

theorem GlobalTheory.HorFrame.exists_ksComb_eq_single : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : GlobalTheory.FlagMod.FlagCover Y} {Z : Comp Xo c} (M : Modif (str₀ X Z) (U₀ X Z) (GlobalTheory.FlagTan.dimFlag Dw)), (∀ (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), KSIso (psiSet H) y) → ∀ (k : X.F.J) {W₁ : M.X.Opens} (hW₁ : IsAffineOpen W₁), W₁ ≤ M.off → ∀ (hk₁ : ⊤ ≤ (tau hW₁ ≫ toFlag M) ⁻¹ᵁ X.F.U k) [Algebra c.F Γ(M.X, W₁)] (Q₀ : FrPt Xo c Γ(M.X, W₁)), X.F.ChartFr k _ hk₁ Q₀ → ∀ (d : Fin (dimFlag Dw) → (Γ(M.X, W₁) →+* DualNumber Γ(M.X, W₁))), (∀ a s, (d a s).fst = s) → (∀ (K : Type) [Field K] (θ : Γ(M.X, W₁) →+* DualNumber K), ∃ m : Fin (dimFlag Dw) → K, ∀ s, (θ s).snd = ∑ b, m b * (TrivSqZeroExt.fstHom K K K).toRingHom (θ (d b s).snd)) → ∀ (Mx : Fin (dimFlag Dw) → HIx Dw (psiSet H) → Γ(M.X, W₁)), (∀ a (K : Type) [Field K] [Algebra c.F K] (ψ : Γ(M.X, W₁) →ₐ[c.F] K) (y' : FrPt Xo c K), FrMap ψ Q₀ y' → GlobalTheory.FlagTan.IsKS (psiSet H) y' (spMap (dualMap ψ.toRingHom) ≫ spMap (d a) ≫ Q₀.x) (ψ ∘ Mx a)) → ∀ (K : Type) [Field K] (ψ : Γ(M.X, W₁) →+* K) (b : HIx Dw (psiSet H)), ∃ m : Fin (dimFlag Dw) → K, ∑ a, m a • (ψ ∘ Mx a) = Pi.single b 1 := by
  intro E _ _ _ H Dw l Xo c Y X Z M hKS k W₁ hW₁ hoff hk₁ _ Q₀ hQ₀ d hd hspan Mx hMx K _ ψ b
  letI : Algebra c.F K := (ψ.comp (algebraMap c.F Γ(M.X, W₁))).toAlgebra
  let ψA : Γ(M.X, W₁) →ₐ[c.F] K := { ψ with commutes' := fun _ => rfl }
  obtain ⟨Qp, hQp⟩ := GlobalTheory.FlagMod.exists_frMap ψA Q₀
  have hk : ⊤ ≤ ((spMap ψ ≫ tau hW₁) ≫ toFlag M) ⁻¹ᵁ X.F.U k := by
    rw [Category.assoc]; exact le_preimage_comp _ hk₁
  have hch : X.F.ChartFr k _ hk Qp := hQ₀.frMap hQp (Category.assoc _ _ _).symm hk
  have e : (spMap ψ ≫ tau hW₁) ≫ toFlag M = X.ptY Qp := GlobalTheory.FlagMod.FlagCover.eq_ptY hch.lies
  have ho : ⊤ ≤ (spMap ψ ≫ tau hW₁) ⁻¹ᵁ M.off := le_preimage_comp _ (tau_le hW₁ hoff)
  obtain ⟨v, hv⟩ := (hKS K Qp).exists_isTanFrame
  obtain ⟨zv, hzv, hzO⟩ := GlobalTheory.CompHS.exists_tanLift M (hv.isDef (.inl b)) e ho
  have hzW : ⊤ ≤ zv ⁻¹ᵁ W₁ := hzO W₁ (le_preimage_comp _ (tau_le hW₁ le_rfl))
  have hθ : spMap (ev zv W₁ hzW) ≫ tau hW₁ = zv := spMap_ev zv hW₁ hzW
  have hred : spMap (GlobalTheory.FlagTan.red c K).toRingHom ≫ zv = spMap ψ ≫ tau hW₁ := by
    have hU : ⊤ ≤ ((spMap ψ ≫ tau hW₁) ≫ M.σ) ⁻¹ᵁ U₀ X Z := fun s _ => by
      have := ho (Set.mem_univ s)
      rw [M.off_eq] at this
      exact this
    refine (M.existsUnique_lift _ hU).unique ?_ rfl
    rw [← cancel_mono (inc₀ X Z)]
    have h1 : zv ≫ M.σ ≫ inc₀ X Z = X.ptY (v (.inl b)) := hzv
    have h2 : ((spMap ψ ≫ tau hW₁) ≫ M.σ) ≫ inc₀ X Z = X.ptY Qp := by
      rw [← e, Category.assoc]
    rw [h2, Category.assoc, Category.assoc, h1]
    exact X.ptY_frMap (hv.isDef (.inl b))
  have hfst : ∀ s, (ev zv W₁ hzW s).fst = ψ s := by
    have h1 := ev_spMap (GlobalTheory.FlagTan.red c K).toRingHom zv W₁ hzW
      (by rw [hred]; exact le_preimage_comp _ (tau_le hW₁ le_rfl))
    have h2 := ev_spMap_tau hW₁ ψ (le_preimage_comp _ (tau_le hW₁ le_rfl))
    rw [ev_congr hred _ _ (le_preimage_comp _ (tau_le hW₁ le_rfl)), h2] at h1
    intro s
    have := congrArg (fun f : Γ(M.X, W₁) →+* K => f s) h1
    simp only [RingHom.comp_apply] at this
    rw [this]
    rfl
  obtain ⟨m, hm⟩ := hspan K (ev zv W₁ hzW)
  have hsnd : ∀ s, (ev zv W₁ hzW s).snd = ∑ a, m a * ψ (d a s).snd := fun s => by
    rw [hm s]
    exact Finset.sum_congr rfl fun a _ => by rw [← hfst]; rfl
  obtain ⟨w, hwD, hwKS, hwpt⟩ := GlobalTheory.T.exists_chart_frame_deformation_of_derivation_combination M hKS k hW₁ hk₁ Q₀ hQ₀ d hd Mx hMx K ψ hk Qp hch
    (ev zv W₁ hzW) m hfst hsnd
  have hpt : X.ptY w = X.ptY (v (.inl b)) := by
    rw [← hwpt, ← Category.assoc, hθ, hzv]
  have hx : w.x = (v (.inl b)).x := by
    have h1 := (X.lies_ptY w).1
    have h2 := (X.lies_ptY (v (.inl b))).1
    rw [hpt] at h1
    rw [← frX_fst, ← frX_fst, xF_ext (Y := Y) (frX_snd w) (frX_snd _) (h1.symm.trans h2)]
  obtain ⟨M', -, hu⟩ := (hKS K Qp).existsUnique hwD.isTanX
  refine ⟨m, (hu _ hwKS).trans (hu _ ?_).symm⟩
  rw [hx]
  exact (hv.1 b).2

theorem GlobalTheory.HorFrame.exists_basicOpen_det_ks : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : GlobalTheory.FlagMod.FlagCover Y} {Z : Comp Xo c} (M : Modif (str₀ X Z) (U₀ X Z) (GlobalTheory.FlagTan.dimFlag Dw)), (∀ (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), KSIso (psiSet H) y) → ∀ (k : X.F.J) {W₁ : M.X.Opens} (hW₁ : IsAffineOpen W₁), W₁ ≤ M.off → ∀ (hk₁ : ⊤ ≤ (tau hW₁ ≫ toFlag M) ⁻¹ᵁ X.F.U k) [Algebra c.F Γ(M.X, W₁)] (Q₀ : FrPt Xo c Γ(M.X, W₁)), X.F.ChartFr k _ hk₁ Q₀ → ∀ (d : Fin (dimFlag Dw) → (Γ(M.X, W₁) →+* DualNumber Γ(M.X, W₁))), (∀ a s, (d a s).fst = s) → (∀ (K : Type) [Field K] (θ : Γ(M.X, W₁) →+* DualNumber K), ∃ m : Fin (dimFlag Dw) → K, ∀ s, (θ s).snd = ∑ b, m b * (TrivSqZeroExt.fstHom K K K).toRingHom (θ (d b s).snd)) → ∀ (Mx : Fin (dimFlag Dw) → HIx Dw (psiSet H) → Γ(M.X, W₁)), (∀ a (K : Type) [Field K] [Algebra c.F K] (ψ : Γ(M.X, W₁) →ₐ[c.F] K) (y' : FrPt Xo c K), FrMap ψ Q₀ y' → GlobalTheory.FlagTan.IsKS (psiSet H) y' (spMap (dualMap ψ.toRingHom) ≫ spMap (d a) ≫ Q₀.x) (ψ ∘ Mx a)) → ∀ (p : M.X), p ∈ W₁ → ∃ B : Matrix (HIx Dw (psiSet H)) (Fin (dimFlag Dw)) Γ(M.X, W₁), p ∈ M.X.basicOpen (B * Matrix.of (fun a h => Mx a h)).det := by
  intro E _ _ _ H Dw l Xo c Y X Z M hKS k W₁ hW₁ hoff hk₁ _ Q₀ hQ₀ d hd hspan Mx hMx p hp
  obtain ⟨K, hK, ψ, hbo, hden⟩ := GlobalTheory.T.exists_ringHom_field_common_denom_of_mem_isAffineOpen hW₁ p hp
  choose m hm using fun b => GlobalTheory.HorFrame.exists_ksComb_eq_single M hKS k hW₁ hoff hk₁ Q₀ hQ₀ d hd hspan Mx hMx K ψ b
  obtain ⟨a, t, ht, hat⟩ := hden (HIx Dw (psiSet H) × Fin (dimFlag Dw)) (fun bc => m bc.1 bc.2)
  refine ⟨Matrix.of fun b c => a (b, c), hbo _ ?_⟩
  have hmap : ((Matrix.of fun b c => a (b, c)) * Matrix.of (fun a h => Mx a h)).map ψ =
      Matrix.scalar (HIx Dw (psiSet H)) (ψ t) := by
    ext b h
    have e := congrFun (hm b) h
    simp only [Finset.sum_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul] at e

    simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.of_apply, map_sum, map_mul, Matrix.scalar_apply,
    Matrix.diagonal_apply]
    simp only [← hat]
    calc ∑ x, m b x * ψ t * ψ (Mx x h) = ψ t * ∑ x, m b x * ψ (Mx x h) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun x _ => by ring
      _ = _ := by
          rw [e, Pi.single_apply]
          by_cases hh : h = b
          · subst hh; simp
          · simp [hh, Ne.symm hh]
  rw [RingHom.map_det, RingHom.mapMatrix_apply, hmap, Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const]
  exact pow_ne_zero _ ht
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenKodairaSpencerLeftInverseStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.TangentOrigin
open GlobalTheory.FlagMod GlobalTheory.TopForm
open GlobalTheory.FlagTan (dimFlag psiSet TIx HIx VIx IsTanFrame IsDef IsVert KSIso kap)
open GlobalTheory.AllWt (exOf)
open scoped Classical

theorem _root_.GlobalTheory.T.exists_basicOpen_kodairaSpencer_left_inverse : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : GlobalTheory.FlagMod.FlagCover Y} {Z : Comp Xo c} (M : Modif (str₀ X Z) (U₀ X Z) (GlobalTheory.FlagTan.dimFlag Dw)), (∀ (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), KSIso (psiSet H) y) → ∀ (k : X.F.J) {W₁ : M.X.Opens} (hW₁ : IsAffineOpen W₁), W₁ ≤ M.off → ∀ (hk₁ : ⊤ ≤ (tau hW₁ ≫ toFlag M) ⁻¹ᵁ X.F.U k) [Algebra c.F Γ(M.X, W₁)] (Q₀ : FrPt Xo c Γ(M.X, W₁)), X.F.ChartFr k _ hk₁ Q₀ → ∀ (d : Fin (dimFlag Dw) → (Γ(M.X, W₁) →+* DualNumber Γ(M.X, W₁))), (∀ a s, (d a s).fst = s) → (∀ (K : Type) [Field K] (θ : Γ(M.X, W₁) →+* DualNumber K), ∃ m : Fin (dimFlag Dw) → K, ∀ s, (θ s).snd = ∑ b, m b * (TrivSqZeroExt.fstHom K K K).toRingHom (θ (d b s).snd)) → ∀ (Mx : Fin (dimFlag Dw) → HIx Dw (psiSet H) → Γ(M.X, W₁)), (∀ a (K : Type) [Field K] [Algebra c.F K] (ψ : Γ(M.X, W₁) →ₐ[c.F] K) (y' : FrPt Xo c K), FrMap ψ Q₀ y' → GlobalTheory.FlagTan.IsKS (psiSet H) y' (spMap (dualMap ψ.toRingHom) ≫ spMap (d a) ≫ Q₀.x) (ψ ∘ Mx a)) → ∀ (p : M.X), p ∈ W₁ → ∃ B : Matrix (HIx Dw (psiSet H)) (Fin (dimFlag Dw)) Γ(M.X, W₁), p ∈ M.X.basicOpen (B * Matrix.of (fun a h => Mx a h)).det := by
  first | exact @GlobalTheory.HorFrame.exists_basicOpen_det_ks | exact GlobalTheory.HorFrame.exists_basicOpen_det_ks | (intros; apply GlobalTheory.HorFrame.exists_basicOpen_det_ks <;> assumption)
end
end
