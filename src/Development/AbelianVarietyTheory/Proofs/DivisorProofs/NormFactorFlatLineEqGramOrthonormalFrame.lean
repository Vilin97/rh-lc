module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameCoord
public import Development.AbelianVarietyTheory.Definitions.Divisors.VolMeasureOfAdd
public import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsotropicCoefficientSplitting
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ImDiagEqTrace
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
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
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.PeriodicSchwarzLemma
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameGramDetEqUniformizationHermFormStatement
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodFrameLimitsOfOrbit
import Formalism.LocalToGlobal.ProjectiveLattices.FnDefC
import Formalism.LocalToGlobal.ProjectiveLattices.UnifFrDet
import Mathlib.Tactic.Basify
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.SupAtUnit
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetGramLowerTriangularCoordVecRe

section

@[expose] public section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
open scoped Matrix

theorem GlobalTheory.det_gram_lowerTriangular_coordVec_re : ∀ (g m : ℕ) (f : Fin m → Fin g), Function.Injective f → ∀ (a : ℝ) (C : Fin m → Fin m → ℂ), (∀ i j : Fin m, i < j → C i j = 0) → (Matrix.of fun i j : Fin m => (Real.pi : ℂ) * hermForm ((a : ℂ) • (1 : Matrix (Fin g) (Fin g) ℂ)) (∑ l, C j l • Pi.single (f l) (1 : ℂ)) (∑ l, C i l • Pi.single (f l) (1 : ℂ))).det.re = (Real.pi * a) ^ m * ∏ i, ‖C i i‖ ^ 2 := by
  intro g m f hf a C hC
  classical
  set A : Matrix (Fin m) (Fin m) ℂ := Matrix.of C with hA
  set P : Matrix (Fin m) (Fin g) ℂ := Matrix.of fun l k => (Pi.single (f l) (1:ℂ) : Fin g → ℂ) k with hP
  have hX : ∀ i, (∑ l, C i l • Pi.single (f l) (1:ℂ)) = fun k => (A * P) i k := by
    intro i; ext k; simp [Matrix.mul_apply, hP, hA, Finset.sum_apply]
  have hPP : P * Pᴴ = 1 := by
    ext l l'
    simp only [Matrix.mul_apply, hP, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.one_apply]
    simp [Pi.single_apply, hf.eq_iff, eq_comm]
  have hH : ∀ u v : Fin g → ℂ, hermForm ((a : ℂ) • (1 : Matrix (Fin g) (Fin g) ℂ)) u v = (a:ℂ) * (u ⬝ᵥ star v) := by
    intro u v
    rw [hermForm, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul]
  have hE : (Matrix.of fun i j : Fin m => (Real.pi : ℂ) * hermForm ((a : ℂ) • (1 : Matrix (Fin g) (Fin g) ℂ)) (∑ l, C j l • Pi.single (f l) (1 : ℂ)) (∑ l, C i l • Pi.single (f l) (1 : ℂ))) = ((Real.pi : ℂ) * a) • (A * Aᴴ)ᵀ := by
    ext i j
    rw [Matrix.of_apply, hX, hX, hH]
    have : (fun k => (A * P) j k) ⬝ᵥ star (fun k => (A * P) i k) = ((A * P) * (A * P)ᴴ) j i := by
      rw [Matrix.mul_apply]; simp only [dotProduct, Matrix.conjTranspose_apply, Pi.star_apply]
    rw [this, Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc P, hPP, Matrix.one_mul]
    rw [Matrix.smul_apply, Matrix.transpose_apply, smul_eq_mul]; ring
  have hlow : A.BlockTriangular OrderDual.toDual := by
    intro i j hij
    exact hC i j hij
  rw [hE, Matrix.det_smul, Matrix.det_transpose, Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_of_lowerTriangular A hlow]
  have : (∏ i, A i i) * star (∏ i, A i i) = ((∏ i, ‖C i i‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    simp [hA, Finset.prod_pow, norm_prod]
  rw [this, Fintype.card_fin]
  rw [show ((Real.pi : ℂ) * a) ^ m = (((Real.pi * a) ^ m : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_mul, Complex.ofReal_re]
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetGramLowerTriangularCoordVecReStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

theorem _root_.GlobalTheory.T.det_gram_lowerTriangular_re_eq_pi_mul_pow : ∀ (g m : ℕ) (f : Fin m → Fin g), Function.Injective f → ∀ (a : ℝ) (C : Fin m → Fin m → ℂ), (∀ i j : Fin m, i < j → C i j = 0) → (Matrix.of fun i j : Fin m => (Real.pi : ℂ) * hermForm ((a : ℂ) • (1 : Matrix (Fin g) (Fin g) ℂ)) (∑ l, C j l • Pi.single (f l) (1 : ℂ)) (∑ l, C i l • Pi.single (f l) (1 : ℂ))).det.re = (Real.pi * a) ^ m * ∏ i, ‖C i i‖ ^ 2 := by
  first | exact @GlobalTheory.det_gram_lowerTriangular_coordVec_re | exact GlobalTheory.det_gram_lowerTriangular_coordVec_re | (intros; apply GlobalTheory.det_gram_lowerTriangular_coordVec_re <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneousNormFactorFlatLineOrthonormalFrame

section

@[expose] public section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.OrthoFlatFac

theorem sum_wtOf_flatWt {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    (Dw : Datum H) (τ : Psi H) :
    (∑ ρ : E →+* ℂ, ∑ i : Fin (Dw.mult ρ), (((wtOf Dw (flatWt Dw τ) 0).1 (ρ, i) : ℤ) : ℝ)) = (Dw.q : ℝ) - Dw.p := by
  classical
  have key : ∀ ρ : E →+* ℂ, ∑ i : Fin (Dw.mult ρ), (((wtOf Dw (flatWt Dw τ) 0).1 (ρ, i) : ℤ) : ℝ) =
      (if ρ = conjEmb τ.1 then (Dw.q : ℝ) else 0) - if ρ = τ.1 then (Dw.p : ℝ) else 0 := fun ρ => by
    by_cases h : ρ (H.rt : E) = H.rt0
    · have hm : Dw.mult ρ = Dw.p := if_pos h
      have h1 : ρ ≠ conjEmb τ.1 := fun e => conj_not_mem τ (e ▸ h)
      have h2 : ∀ i : Fin (Dw.mult ρ), (wtOf Dw (flatWt Dw τ) 0).1 (ρ, i) = if ρ = τ.1 then -1 else 0 := fun i =>
        (wtOf_big (flatWt Dw τ) 0 ⟨ρ, h⟩ i (hm ▸ i.2)).trans (by simp [flatWt, parWt, Subtype.ext_iff])
      simp only [h2]
      split_ifs <;> simp_all
    · have hm : Dw.mult ρ = Dw.q := if_neg h
      have h1 : ρ ≠ τ.1 := fun e => h (e ▸ τ.2)
      have h2 : ∀ i : Fin (Dw.mult ρ), (wtOf Dw (flatWt Dw τ) 0).1 (ρ, i) = if ρ = conjEmb τ.1 then 1 else 0 :=
        fun i => by
          have := wtOf_small (flatWt Dw τ) 0 ⟨_, conj_mem h⟩ i (hm ▸ i.2)
          simp only [Formalism.L2.Pj.conjEmb_conjEmb] at this
          rw [this]
          by_cases e : ρ = conjEmb τ.1
          · simp [flatWt, parWt, e, Formalism.L2.Pj.conjEmb_conjEmb]
          · have : conjEmb ρ ≠ τ.1 := fun e' => e (by rw [← e', Formalism.L2.Pj.conjEmb_conjEmb])
            simp [flatWt, parWt, Subtype.ext_iff, e, this]
      simp only [h2]
      split_ifs <;> simp_all
  simp only [key, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem homFac_flatWt_ortho : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (x : ℝ)
    (τ : Psi H) (k : U.Comp) (w : (U.X k).dom), (U.X k).IsOrtho w.1 →
    GlobalTheory.CompHS.homFac U x (flatWt Dw τ) k w = Real.exp (((Dw.p : ℝ) - Dw.q) / 2 * Real.log (2 * Real.pi * x)) := by
  intro E _ _ _ H Dw l Xo c σ r U x τ k w ho
  rw [GlobalTheory.CompHS.homFac, GlobalTheory.OrbitNfac.nfac_ortho _ ho, mul_one, lieFacZ, sum_wtOf_flatWt]
  congr 1
  ring

end GlobalTheory.OrthoFlatFac
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneousNormFactorFlatLineOrthonormalFrameStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

theorem _root_.GlobalTheory.T.homogeneousNormFactor_flatLine_orthonormalFrame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (x : ℝ) (τ : Psi H) (k : U.Comp) (w : (U.X k).dom), (U.X k).IsOrtho w.1 → GlobalTheory.CompHS.homFac U x (flatWt Dw τ) k w = Real.exp (((Dw.p : ℝ) - Dw.q) / 2 * Real.log (2 * Real.pi * x)) := by
  first | exact @GlobalTheory.OrthoFlatFac.homFac_flatWt_ortho | exact GlobalTheory.OrthoFlatFac.homFac_flatWt_ortho | (intros; apply GlobalTheory.OrthoFlatFac.homFac_flatWt_ortho <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormDiagonalTorusCharacterFlatLineWeight

section

@[expose] public section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompHS.FlatDiag

theorem norm_diagChar_flatWt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (σ : c.F →+* ℂ) (τ : Psi H) (t : Ix Dw → (CAt σ)ˣ), ‖GlobalTheory.CompHS.diagChar (exOf Dw (flatWt Dw τ) 0) t‖ = (∏ j : Fin (Dw.mult (conjEmb τ.1)), ‖toC ((t (some ⟨conjEmb τ.1, j⟩) : CAt σ))‖) / ∏ i : Fin (Dw.mult τ.1), ‖toC ((t (some ⟨τ.1, i⟩) : CAt σ))‖ := by
  classical
  intro E _ _ _ H Dw l c σ τ t
  set e := exOf Dw (flatWt Dw τ) 0 with he_def
  have hne : τ.1 ≠ conjEmb τ.1 := fun h => conj_not_mem τ (h ▸ τ.2)
  have hE : ∀ (ρ : E →+* ℂ) (i : Fin (Dw.mult ρ)),
      e (some ⟨ρ, i⟩) = if ρ = τ.1 then -1 else if ρ = conjEmb τ.1 then 1 else 0 := by
    intro ρ i
    obtain ⟨n, hi⟩ := i
    simp only [he_def, exOf, exZ, wtOf, flatWt, parWt, Datum.mult] at hi ⊢
    by_cases h : ρ (H.rt : E) = H.rt0
    · rw [if_pos h] at hi
      rw [dite_eq_left h, dite_eq_left hi]
      have h2 : ρ ≠ conjEmb τ.1 := fun e => conj_not_mem τ (e ▸ h)
      by_cases h1 : ρ = τ.1
      · subst h1
        simp
      · have h3 : (⟨ρ, h⟩ : Psi H) ≠ τ := fun e => h1 (congrArg Subtype.val e)
        simp [h1, h2, h3]
    · rw [if_neg h] at hi
      rw [dite_eq_right h]
      have h1 : ρ ≠ τ.1 := fun e => h (e ▸ τ.2)
      by_cases h' : conjEmb ρ (H.rt : E) = H.rt0
      · rw [dite_eq_left h', dite_eq_left hi]
        by_cases h2 : ρ = conjEmb τ.1
        · have h3 : (⟨conjEmb ρ, h'⟩ : Psi H) = τ := Subtype.ext (show conjEmb ρ = τ.1 by rw [h2, conjEmb_conjEmb])
          rw [if_pos h3, if_neg h1, if_pos h2]
          norm_num
        · have h3 : (⟨conjEmb ρ, h'⟩ : Psi H) ≠ τ := fun e => h2 (by
            rw [← congrArg Subtype.val e, conjEmb_conjEmb])
          rw [if_neg h3, if_neg h1, if_neg h2]
          norm_num
      · rw [dite_eq_right h']
        have h2 : ρ ≠ conjEmb τ.1 := fun e => h' (by rw [e, conjEmb_conjEmb]; exact τ.2)
        simp [h1, h2]
  have e0 : e none = 0 := by simp [he_def, exOf, exZ, wtOf_snd]
  let f : (CAt σ)ˣ →* ℂˣ := Units.map (MonoidHom.id ℂ)
  have hf : ∀ u : (CAt σ)ˣ, ((f u : ℂˣ) : ℂ) = toC (u : CAt σ) := fun _ => rfl
  have e₁ : GlobalTheory.CompHS.diagChar e t = ((∏ ix, f (t ix) ^ e ix : ℂˣ) : ℂ) := by
    have : (∏ ix, f (t ix) ^ e ix) = f (∏ ix, t ix ^ e ix) := by simp only [map_prod, map_zpow]
    rw [this, hf]
    rfl
  let g : (E →+* ℂ) → ℝ := fun ρ => ∏ i : Fin (Dw.mult ρ), ‖toC ((t (some ⟨ρ, i⟩) : CAt σ))‖ ^ e (some ⟨ρ, i⟩)
  have e₂ : ‖GlobalTheory.CompHS.diagChar e t‖ = ∏ ρ, g ρ := by
    rw [e₁, Units.coe_prod, norm_prod, Fintype.prod_option, e0, zpow_zero, Units.val_one, norm_one, one_mul,
      Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun ρ _ => Finset.prod_congr rfl fun i _ => ?_
    rw [Units.val_zpow_eq_zpow_val, norm_zpow, hf]
  have e₃ : ∏ ρ, g ρ = g τ.1 * g (conjEmb τ.1) := by
    rw [← Finset.prod_pair hne]
    refine (Finset.prod_subset (Finset.subset_univ _) fun ρ _ hρ => ?_).symm
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hρ
    exact Finset.prod_eq_one fun i _ => by rw [hE, if_neg hρ.1, if_neg hρ.2, zpow_zero]
  have gτ : g τ.1 = (∏ i : Fin (Dw.mult τ.1), ‖toC ((t (some ⟨τ.1, i⟩) : CAt σ))‖)⁻¹ := by
    rw [← Finset.prod_inv_distrib]
    exact Finset.prod_congr rfl fun i _ => by rw [hE, if_pos rfl, zpow_neg_one]
  have gc : g (conjEmb τ.1) = ∏ j : Fin (Dw.mult (conjEmb τ.1)), ‖toC ((t (some ⟨conjEmb τ.1, j⟩) : CAt σ))‖ :=
    Finset.prod_congr rfl fun i _ => by rw [hE, if_neg hne.symm, if_pos rfl, zpow_one]
  rw [e₂, e₃, gτ, gc, div_eq_mul_inv, mul_comm]

end GlobalTheory.CompHS.FlatDiag
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormDiagonalTorusCharacterFlatLineWeightStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

theorem _root_.GlobalTheory.T.norm_diagonalTorusCharacter_flatLineWeight : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (σ : c.F →+* ℂ) (τ : Psi H) (t : Ix Dw → (CAt σ)ˣ), ‖GlobalTheory.CompHS.diagChar (exOf Dw (flatWt Dw τ) 0) t‖ = (∏ j : Fin (Dw.mult (conjEmb τ.1)), ‖toC ((t (some ⟨conjEmb τ.1, j⟩) : CAt σ))‖) / ∏ i : Fin (Dw.mult τ.1), ‖toC ((t (some ⟨τ.1, i⟩) : CAt σ))‖ := by
  first | exact @GlobalTheory.CompHS.FlatDiag.norm_diagChar_flatWt | exact GlobalTheory.CompHS.FlatDiag.norm_diagChar_flatWt | (intros; apply GlobalTheory.CompHS.FlatDiag.norm_diagChar_flatWt <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormFactorFlatLineEqGramOrthonormalFrame

section

@[expose] public section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

noncomputable section

namespace GlobalTheory.PtDegOrtho

theorem homFac_eq_gram_ortho : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ (τ : Psi H) (K : Type) [Field K] [NumberField K] [Algebra c.F K] (y : FrPt Xo c K) (B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (t₀ : SAB H (Sp K)) (m1 : SABMap t₀ Xo.univ.t y.x) (m2 : SABMap t₀ B.t (spMap (algebraMap (𝓞 K) K))) (F : GlobalTheory.CM.GenFib B.pol) (h : ReciprocityTheory.GeometryOfNumbersTheory.HermFam K (Fin F.P₀.g → K)), F.IsHerm h → ∀ (u : Fin (Dw.mult τ.1) → Fin F.P₀.g → K) (u' : Fin (Dw.mult (conjEmb τ.1)) → Fin F.P₀.g → K), GlobalTheory.PtDeg.FrameCoord y m1 m2 F τ.1 u → GlobalTheory.PtDeg.FrameCoord y m1 m2 F (conjEmb τ.1) u' → ∀ (σ : K →+* ℂ), GoodEmb c (σ.comp (algebraMap c.F K)) → ∀ (φ : K →ₐ[c.F] CAt (σ.comp (algebraMap c.F K))), (∀ a, toC (φ a) = σ a) → ∀ (z : FrPt Xo c (CAt (σ.comp (algebraMap c.F K)))), FrMap φ y z → ∀ (k : (U (σ.comp (algebraMap c.F K))).Comp) (w : ((U (σ.comp (algebraMap c.F K))).X k).dom) (t : Ix Dw → (CAt (σ.comp (algebraMap c.F K)))ˣ), ((U (σ.comp (algebraMap c.F K))).X k).IsOrtho w.1 → FrBor t ((U (σ.comp (algebraMap c.F K))).un k w) z → GlobalTheory.CompHS.homFac (U (σ.comp (algebraMap c.F K))) x (flatWt Dw τ) k w = ‖GlobalTheory.CompHS.diagChar (exOf Dw (flatWt Dw τ) 0) t‖ * Real.sqrt (h.gram σ u).det.re / Real.sqrt (h.gram σ u').det.re := by
  intro E _ _ _ H Dw l Xo c r U x hL τ K _ _ _ y B t₀ m1 m2 F h hh u u' hu hu' σ hσ φ hφ z hz k w t hort hbor
  have hU := hL.unf _ hσ
  obtain ⟨W⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.nonempty_unfAt hU k w
  obtain ⟨Wu⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.nonempty_unitAt W (ReciprocityTheory.ChartRestriction.G.PullbackSections.PfSupAtUnit.dmin_ortho _ hort)
  have hHm := GlobalTheory.OrthoHerm.hm_eq_smul_one E H Dw l Xo c _ r (U _) x hσ hU k w W Wu (hL.xi _ hσ k) hort
  obtain ⟨hzx, hcomb, -⟩ := hbor
  choose C hCi hCup hCc using hcomb
  have hp : Dw.mult τ.1 = Dw.p := by unfold Datum.mult; rw [if_pos τ.2]
  have hq : Dw.mult (conjEmb τ.1) = Dw.q := by unfold Datum.mult; rw [if_neg (conj_not_mem τ)]

  have hx : 0 < x := by
    have hne : Nonempty (Σ ρ : E →+* ℂ, Fin (Dw.mult ρ)) := by
      rcases Nat.eq_zero_or_pos Dw.p with h0 | h0
      · have hq1 : 0 < Dw.q := by have := hL.pos; omega
        exact ⟨⟨conjEmb τ.1, ⟨0, hq ▸ hq1⟩⟩⟩
      · exact ⟨⟨τ.1, ⟨0, hp ▸ h0⟩⟩⟩
    obtain ⟨j0⟩ := hne
    have h1 := Wu.pos (Pi.single (W.e.symm j0) 1) (by simp)
    rw [hHm] at h1
    have h2 : hermForm (((2 * x : ℝ) : ℂ) • (1 : Matrix (Fin W.g) (Fin W.g) ℂ)) (Pi.single (W.e.symm j0) 1)
        (Pi.single (W.e.symm j0) 1) = ((2 * x : ℝ) : ℂ) := by
      simp [hermForm, Matrix.smul_mulVec, dotProduct, Pi.single_apply]
    rw [h2, Complex.ofReal_re] at h1
    linarith
  have key : ∀ (ρ : E →+* ℂ) (v : Fin (Dw.mult ρ) → Fin F.P₀.g → K), GlobalTheory.PtDeg.FrameCoord y m1 m2 F ρ v →
      (h.gram σ v).det.re = (2 * Real.pi * x) ^ (Dw.mult ρ) *
        (∏ i : Fin (Dw.mult ρ), ‖toC ((t (some ⟨ρ, i⟩) : CAt (σ.comp (algebraMap c.F K))))‖) ^ 2 := by
    intro ρ v hv
    rw [GlobalTheory.T.frame_gram_det_eq_uniformization_hermForm E H Dw l Xo c r U x hL K y B t₀ m1 m2 F h hh ρ v hv σ hσ φ hφ z hz k w W Wu hzx (C ρ) (hCc ρ), hHm,
      GlobalTheory.T.det_gram_lowerTriangular_re_eq_pi_mul_pow W.g (Dw.mult ρ) (fun l => W.e.symm ⟨ρ, l⟩) (fun a b e => by simpa using e) (2 * x)
        (fun i j => toC (C ρ i j)) (fun i j hij => by simp only [hCup ρ i j hij]; rfl), ← Finset.prod_pow]
    simp only [hCi]
    congr 1
    ring
  rw [GlobalTheory.T.homogeneousNormFactor_flatLine_orthonormalFrame E H Dw l Xo c _ r (U _) x τ k w hort, GlobalTheory.T.norm_diagonalTorusCharacter_flatLineWeight E H Dw l c _ τ t, key _ u hu, key _ u' hu']
  have e1 : (2 * Real.pi * x) ^ (Dw.mult τ.1) = (2 * Real.pi * x) ^ Dw.p := by rw [hp]
  have e2 : (2 * Real.pi * x) ^ (Dw.mult (conjEmb τ.1)) = (2 * Real.pi * x) ^ Dw.q := by rw [hq]
  rw [e1, e2]
  have hpos : ∀ ρ : E →+* ℂ, 0 < ∏ i : Fin (Dw.mult ρ), ‖toC ((t (some ⟨ρ, i⟩) : CAt (σ.comp (algebraMap c.F K))))‖ :=
    fun ρ => Finset.prod_pos fun i _ => norm_pos_iff.2 (Units.ne_zero (M₀ := ℂ) _)
  have hP := hpos τ.1
  have hP' := hpos (conjEmb τ.1)
  generalize ∏ i : Fin (Dw.mult τ.1), ‖toC ((t (some ⟨τ.1, i⟩) : CAt (σ.comp (algebraMap c.F K))))‖ = P at *
  generalize ∏ i : Fin (Dw.mult (conjEmb τ.1)), ‖toC ((t (some ⟨conjEmb τ.1, i⟩) : CAt (σ.comp (algebraMap c.F K))))‖ = P' at *
  have ha : 0 < 2 * Real.pi * x := by positivity
  have hs : ∀ n : ℕ, Real.sqrt ((2 * Real.pi * x) ^ n) = Real.exp ((n : ℝ) / 2 * Real.log (2 * Real.pi * x)) := by
    intro n
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul ha.le, Real.rpow_def_of_pos ha]
    congr 1
    ring
  rw [Real.sqrt_mul (pow_nonneg ha.le _), Real.sqrt_mul (pow_nonneg ha.le _), Real.sqrt_sq hP.le, Real.sqrt_sq hP'.le,
    hs, hs]
  have hq2 : Real.exp (((Dw.p : ℝ) - Dw.q) / 2 * Real.log (2 * Real.pi * x)) * Real.exp ((Dw.q : ℝ) / 2 * Real.log (2 * Real.pi * x)) =
      Real.exp ((Dw.p : ℝ) / 2 * Real.log (2 * Real.pi * x)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [← hq2]
  field_simp

end GlobalTheory.PtDegOrtho
end
end
end
