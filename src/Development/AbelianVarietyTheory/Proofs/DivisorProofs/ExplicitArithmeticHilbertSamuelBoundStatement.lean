module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
public import Development.AbelianVarietyTheory.Definitions.Divisors.LinearIndependentBasisCoords
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.ArakelovDegreeEqDegreeOfFamily
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TopRankPowers
import Development.AbelianVarietyTheory.Definitions.Divisors.CommGroupMulMulEqMulInvMulMulMul
import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBoundedPolesGlobalData
import Development.AbelianVarietyTheory.Definitions.Divisors.MemSubPtsCutBaseChangeIff
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Development.AbelianVarietyTheory.Definitions.Divisors.InclEquiv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertSamuelFiltrationAtGoodSections
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertSamuelLatticeSystemHypStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormEqOfCsq

section

@[expose] public section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory

noncomputable section

namespace GlobalTheory.IsoDeg

open Module
open scoped ComplexConjugate

variable {K V W : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]

theorem form_eq_of_csq (n : HermFam K V) (n' : HermFam K W) (e : V ≃ₗ[K] W)
    (hc : ∀ σ (m : ℕ) (c : Fin m → ℂ) (g : Fin m → V), csq n σ c g = csq n' σ c fun i => e (g i))
    (σ : K →+* ℂ) (x y : V) : n'.form σ (e x) (e y) = n.form σ x y := by
  have h1 := hc σ 2 ![1, 1] ![x, y]
  have h2 := hc σ 2 ![1, Complex.I] ![x, y]
  have hx := hc σ 1 ![1] ![x]
  have hy := hc σ 1 ![1] ![y]
  simp only [csq, Fin.sum_univ_two, Fin.sum_univ_one, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Matrix.head_cons, map_one, one_mul, mul_one, Complex.add_re] at h1 h2 hx hy
  rw [← n.conj_symm σ x y, ← n'.conj_symm σ (e x) (e y)] at h1 h2
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.I_re, Complex.I_im,
    Complex.conj_I, Complex.neg_re, Complex.neg_im, Complex.mul_im] at h1 h2
  apply Complex.ext
  · linarith
  · nlinarith

theorem deg_map_eq : ∀ (K V W : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] (n : HermFam K V) (n' : HermFam K W) (e : V ≃ₗ[K] W), (∀ σ (m : ℕ) (c : Fin m → ℂ) (g : Fin m → V), csq n σ c g = csq n' σ c fun i => e (g i)) → ∀ L : Submodule (𝓞 K) V, L.FG → deg n' (L.map (e.toLinearMap.restrictScalars (𝓞 K))) = deg n L := by
  intro K V W _ _ _ _ _ _ _ _ _ _ n n' e hc L hL
  set f := e.toLinearMap.restrictScalars (𝓞 K) with hf
  have hfi : Function.Injective f := e.injective
  obtain ⟨v, hv⟩ := exists_isFrame L hL
  have hfv : IsFrame K (L.map f) (fun i => e (v i)) := by
    refine ⟨fun i => ⟨v i, hv.1 i, rfl⟩, hv.2.1.map' e.toLinearMap e.ker, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    have h0 : e x ∈ (Submodule.span K (Set.range v)).map e.toLinearMap := ⟨x, hv.2.2 hx, rfl⟩
    rw [Submodule.map_span, ← Set.range_comp] at h0
    exact h0
  rw [arakelovDegree_eq_degreeOfFamily n' (hL.map f) hfv, arakelovDegree_eq_degreeOfFamily n hL hv]
  unfold degreeOfFamily
  have hs : Submodule.span (𝓞 K) (Set.range fun i => e (v i)) =
      (Submodule.span (𝓞 K) (Set.range v)).map f := by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  have hidx : (Submodule.span (𝓞 K) (Set.range fun i => e (v i))).toAddSubgroup.relIndex
      (L.map f).toAddSubgroup =
      (Submodule.span (𝓞 K) (Set.range v)).toAddSubgroup.relIndex L.toAddSubgroup := by
    have key : ∀ P : Submodule (𝓞 K) V, (P.map f).toAddSubgroup = P.toAddSubgroup.map f.toAddMonoidHom :=
      fun P => by
        ext y
        simp only [Submodule.mem_toAddSubgroup, Submodule.mem_map, AddSubgroup.mem_map,
          LinearMap.toAddMonoidHom_coe]
    rw [hs, key, key]
    exact AddSubgroup.relIndex_map_map_of_injective _ _ hfi
  have hg : ∀ σ, n'.gram σ (fun i => e (v i)) = n.gram σ v := fun σ => by
    ext i j
    simp only [HermFam.gram, Matrix.of_apply]
    exact GlobalTheory.IsoDeg.form_eq_of_csq n n' e hc σ (v i) (v j)
  simp only [hidx, hg]

end GlobalTheory.IsoDeg
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianSystemSlopeBoundOfDeterminantSlopeInequ

section

@[expose] public section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open GlobalTheory.HSShort GlobalTheory.HSChoice MvPolynomial

namespace GlobalTheory.HSShortNum

theorem claimS_to_hsClaimS : ∀ (T D : ℕ) (n Λ β Λ₀ ΛD ΛT δ h h' d deg : ℝ), 1 ≤ D → D + 1 ≤ T → 1 ≤ n → 1 ≤ Λ → 1 ≤ β → 1 ≤ δ →
    h - (Real.log n + 1) / 2 ≤ h' → ClaimS T D n Λ β Λ₀ ΛD ΛT δ h' d deg →
    Formalism.NormVectorIdentities.Items.HSClaimS 26 T D n 1 Λ β ΛD ΛT (Real.log Λ₀) δ h d deg := by
  intro T D n Λ β Λ₀ ΛD ΛT δ h h' d deg hD hT hn hΛ hβ hδ hh hC
  obtain ⟨hz0, hz1, hineq⟩ := hC
  unfold Formalism.NormVectorIdentities.Items.HSClaimS Formalism.NormVectorIdentities.Items.hsZ Formalism.NormVectorIdentities.Items.hsR Formalism.NormVectorIdentities.Items.hsLogRho Formalism.NormVectorIdentities.Items.hsG
  set z : ℝ := 1 - ((T - 1).choose D : ℝ) * δ / d with hz
  refine ⟨hz0, hz1, ?_⟩
  set ρ : ℝ := Real.log Λ + 26 * Real.log (n * (D : ℝ) * 1 * δ * (2 + |h| + Real.log Λ)) with hρ
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hT2 : (2 : ℝ) ≤ T := by
    have : 2 ≤ T := by omega
    exact_mod_cast this
  have hTpos : (0 : ℝ) < T := by linarith
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg hn
  have hlogΛ : 0 ≤ Real.log Λ := Real.log_nonneg hΛ
  have hlogβ : 0 ≤ Real.log β := Real.log_nonneg hβ
  have hβpos : 0 < β := by linarith
  have h1 : Real.log (Real.exp ρ * T) = ρ + Real.log T := by
    rw [Real.log_mul (Real.exp_pos _).ne' hTpos.ne', Real.log_exp]
  have h2 : Real.log (2 * Real.exp ρ * Real.sqrt β) = Real.log 2 + ρ + Real.log β / 2 := by
    rw [Real.log_mul (by positivity) (Real.sqrt_pos.mpr hβpos).ne', Real.log_mul (by norm_num) (Real.exp_pos _).ne',
      Real.log_exp, Real.log_sqrt hβpos.le]
  have hX : (2 : ℝ) ≤ 2 + |h| + Real.log Λ := by have := abs_nonneg h; linarith
  have hprod : 2 * n ≤ n * (D : ℝ) * 1 * δ * (2 + |h| + Real.log Λ) := by
    have a1 : n ≤ n * (D : ℝ) := by nlinarith
    have a2 : n ≤ n * (D : ℝ) * 1 * δ := by nlinarith
    nlinarith
  have hlog2n : Real.log 2 + Real.log n ≤ Real.log (n * (D : ℝ) * 1 * δ * (2 + |h| + Real.log Λ)) := by
    rw [← Real.log_mul (by norm_num) (by linarith)]
    exact Real.log_le_log (by linarith) hprod
  have hl2 := Real.log_two_gt_d9
  have hcst : HSShort.cst n Λ = Real.log n + Real.log Λ + (Real.log n + 1) / 2 := by
    unfold HSShort.cst; rw [Real.log_mul (by linarith) (by linarith)]
  have hc : HSShort.cst n Λ ≤ ρ := by rw [hcst, hρ]; linarith
  have hc0 : 0 ≤ HSShort.cst n Λ := by rw [hcst]; positivity
  rw [h1, h2]
  clear h1 h2 hprod hlog2n hcst hX
  generalize HSShort.cst n Λ = c at *
  clear_value ρ z
  generalize (T : ℝ) = t at *
  generalize (D : ℝ) = e at *
  generalize Real.log t = lt at *
  generalize Real.log n = ln at *
  generalize Real.log β = lb at *
  have hA : t * h - 3 * (e + 1) * |h| - Real.log Λ₀ - 26 * e ^ 2 * (ρ + lt)
        - (t + e + 1) * lb - (t + e ^ 2) * ((e + 1) * (ln + 1) / 2 + 1 + 2)
      ≤ t * h' - e * (e + 1) * c - Real.log Λ₀ - t / 2 * lb := by
    have e1 : t * h - t * ((ln + 1) / 2) ≤ t * h' := by
      have := mul_le_mul_of_nonneg_left hh hTpos.le
      linarith
    have e2 : e * (e + 1) * c ≤ 26 * e ^ 2 * (ρ + lt) := by
      have : e * (e + 1) ≤ 2 * e ^ 2 := by nlinarith
      have hD2 : 0 ≤ e ^ 2 := by positivity
      linarith [mul_le_mul_of_nonneg_right this hc0, mul_nonneg hD2 hlogT, mul_le_mul_of_nonneg_left hc hD2,
        mul_nonneg hD2 hc0]
    have e3 : t / 2 * lb ≤ (t + e + 1) * lb := mul_le_mul_of_nonneg_right (by linarith) hlogβ
    have e4 : t * ((ln + 1) / 2) ≤ (t + e ^ 2) * ((e + 1) * (ln + 1) / 2 + 1 + 2) := by
      have hg : (ln + 1) / 2 ≤ (e + 1) * (ln + 1) / 2 + 1 + 2 := by
        linarith [mul_nonneg (by linarith : (0 : ℝ) ≤ e) (by linarith : (0 : ℝ) ≤ ln + 1)]
      have hT' : t ≤ t + e ^ 2 := by linarith [sq_nonneg e]
      calc t * ((ln + 1) / 2) ≤ t * ((e + 1) * (ln + 1) / 2 + 1 + 2) :=
            mul_le_mul_of_nonneg_left hg hTpos.le
        _ ≤ _ := mul_le_mul_of_nonneg_right hT' (by positivity)
    have e5 : 0 ≤ 3 * (e + 1) * |h| := by positivity
    linarith
  have hB : t * c + t / 2 * lb + Real.log ΛD + Real.log ΛT
      ≤ t * (Real.log 2 + ρ + lb / 2) + Real.log ΛD + Real.log ΛT := by
    have : t * c ≤ t * (Real.log 2 + ρ) := mul_le_mul_of_nonneg_left (by linarith) hTpos.le
    linarith
  have hz1' : 0 ≤ 1 - z := by linarith
  have m1 := mul_le_mul_of_nonneg_left hA hz1'
  have m2 := mul_le_mul_of_nonneg_left hB hz0
  linarith

end GlobalTheory.HSShortNum
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianSystemSlopeBoundOfDeterminantSlopeInequStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open GlobalTheory.HSShort GlobalTheory.HSChoice MvPolynomial

theorem _root_.GlobalTheory.T.hermitianSystemSlopeBound_of_determinantSlopeInequality : ∀ (T D : ℕ) (n Λ β Λ₀ ΛD ΛT δ h h' d deg : ℝ), 1 ≤ D → D + 1 ≤ T → 1 ≤ n → 1 ≤ Λ → 1 ≤ β → 1 ≤ δ → h - (Real.log n + 1) / 2 ≤ h' → ClaimS T D n Λ β Λ₀ ΛD ΛT δ h' d deg → Formalism.NormVectorIdentities.Items.HSClaimS 26 T D n 1 Λ β ΛD ΛT (Real.log Λ₀) δ h d deg := by
  first | exact @GlobalTheory.HSShortNum.claimS_to_hsClaimS | exact GlobalTheory.HSShortNum.claimS_to_hsClaimS | (intros; apply GlobalTheory.HSShortNum.claimS_to_hsClaimS <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertSamuelFiltrationAtGoodSectionsStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open GlobalTheory.HSShort GlobalTheory.HSChoice MvPolynomial

theorem _root_.GlobalTheory.T.hilbertSamuel_filtration_at_good_sections : Quoted → ∀ (F : Type) [Field F] [NumberField F] (X : Data F) (Λ₀ : ℝ), GeoHyp X Λ₀ → ∀ (δ : ℕ) (f : MvPolynomial (Fin (X.D + 1) × Fin X.N) F) (Q : MvPolynomial (Fin X.D × Fin X.N) F), (∀ (E : Type) [Field E] [NumberField E] [Algebra F E] (s : Fin X.D → Fin X.N → E), aeval (fun p : Fin X.D × Fin X.N => s p.1 p.2) Q ≠ 0 → SimpleAt X.toTuple δ f E s) → ∀ s : Fin X.D → Fin X.N → F, eval (fun p : Fin X.D × Fin X.N => s p.1 p.2) Q ≠ 0 → (sysOf X Λ₀).FlatAt δ f s := by
  first | exact @GlobalTheory.HSShort.flatAt_of_simpleAt | exact GlobalTheory.HSShort.flatAt_of_simpleAt | (intros; apply GlobalTheory.HSShort.flatAt_of_simpleAt <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExplicitArithmeticHilbertSamuelBound

section

@[expose] public section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open GlobalTheory.HSShort GlobalTheory.HSChoice MvPolynomial

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSShortTop

theorem geoBound_of_abstract : Quoted → BertiniNF → HeightTie → SlopeBound → GeoBound := by
  intro hQ hB hT hS F _ _ X Λ₀ hG h hh
  obtain ⟨dd, f, hdpos, hf, hfh⟩ := hh
  obtain ⟨hdel, Q, hQ0, hQs⟩ := hB F X.toTuple X.geom hG.bir dd f hf
  have hHyp := GlobalTheory.T.hilbertSamuelLatticeSystem_hyp F X Λ₀ hG
  have hFlat := GlobalTheory.T.hilbertSamuel_filtration_at_good_sections hQ F X Λ₀ hG dd f Q hQs
  have hirr : Irreducible f := GlobalTheory.ChowHt.irreducible_of_irreducible_map hf.irred
  obtain ⟨hpos, hcl⟩ := hS F (Tot X.toGeo) (sysOf X Λ₀) hHyp dd f Q (by omega) hf.homog hirr hQ0 hFlat
  have hfr : Module.finrank F ((sysOf X Λ₀).V (sysOf X Λ₀).T) = X.d := by
    rw [X.d_eq_finrank]; exact (inclEquiv X X.T).finrank_eq.symm
  have hdeg : deg ((sysOf X Λ₀).nm (sysOf X Λ₀).T) ((sysOf X Λ₀).M (sysOf X Λ₀).T) = X.degM X.T := by
    have := GlobalTheory.IsoDeg.deg_map_eq F (X.V X.T) (LinearMap.range (incl X X.T)) (X.nm X.T)
      (comap (X.nm X.T) (inclEquiv X X.T).symm.toLinearMap (inclEquiv X X.T).symm.injective) (inclEquiv X X.T)
      (fun σ m c g => by simp only [csq, HermTools.comap, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]) (X.M X.T) (X.full X.T).fg
    exact this
  have hTie := (hT F X.toHermSys X.abelian₂ hHyp.lat h ⟨dd, f, hdpos, hf, hfh⟩ dd 1 f 1 hf le_rfl one_ne_zero).2
  rw [hfr, hdeg] at hcl
  have hd' : ((X.del : ℤ) : ℝ) = (dd : ℝ) := by rw [← hdel]; push_cast; rfl
  rw [hd']
  refine GlobalTheory.T.hermitianSystemSlopeBound_of_determinantSlopeInequality X.T X.D X.n X.abelian₂ X.beta Λ₀ X.LamD X.LamT dd h _ X.d (X.degM X.T)
    (by exact_mod_cast hHyp.one_le) hHyp.le_T (by exact_mod_cast X.one_le_n) hHyp.lat.one_le hHyp.one_le_beta
    (by exact_mod_cast hdpos) ?_ hcl
  have h2 : h - (Real.log X.n + 1) / 2 ≤ ht X.w X.A f / (((X.D : ℝ) + 1) * dd) := by
    simp at hTie; linarith
  exact h2

end GlobalTheory.HSShortTop
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExplicitArithmeticHilbertSamuelBoundStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open GlobalTheory.HSShort GlobalTheory.HSChoice MvPolynomial

theorem _root_.GlobalTheory.T.explicit_arithmetic_hilbertSamuel_bound : Quoted → BertiniNF → HeightTie → SlopeBound → GeoBound := by
  first | exact @GlobalTheory.HSShortTop.geoBound_of_abstract | exact GlobalTheory.HSShortTop.geoBound_of_abstract | (intros; apply GlobalTheory.HSShortTop.geoBound_of_abstract <;> assumption)
end
end
