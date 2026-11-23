module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.PrimeProj
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.CharConj
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.PiTensorProduct
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
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.NhdsBasisLevelSubgroup
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PAutEx
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.CharConj
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.MapWopWmap
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PEpsIff
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PExpCore
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PExpSum
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.SchurYOffClrHolds
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanInfinitePlacesWeightRepresentationEqTop
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightEqOfFinitePartNeBot
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankWsp
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PTrSch
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueWeightDefiniteUnitaryAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinitePartAtOwnWeightNeBot
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsAutomorphicOfWeightOfNonzeroFixedFinPartForm
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PWtCore

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.PVecWt

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU GlobalTheory.LKTrip GlobalTheory.LKDef GlobalTheory.LKMid Formalism.BasicNotions
open UpperTheory.Gal.CertificateRingHomMap
open scoped Classical

namespace UpperTheory.Gal.Int.Geo.Pl

theorem vecEx_of (h0 : SeedGU) (h1 : WtAt) : VecEx := by
  intro E _ _ _ n l d hn hd x hx U hU w₀ hw₀ hT Up hUp hu
  obtain ⟨e, J, θ, χ, hJo, hJc, htf, -, -, hcusp, hφ⟩ := hT
  let π : AutSub E n := ⟨U, hU⟩
  obtain ⟨W, hW⟩ := (h1 E n hn π).1
  let m : InfinitePlace E → ℕ := fun v => ∑ i, ((W v).w i).natAbs
  have hm : ∀ v i, 0 ≤ (W v).w i + m v := fun v i => by
    have : ((W v).w i).natAbs ≤ m v := Finset.single_le_sum (f := fun i => ((W v).w i).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    omega
  obtain ⟨S, Kw, Φ, κ, a1, a2, a3, a4, a5, a6, a7, a8⟩ := h0 E n hn d x hd hx π W hW (∑ v, ((∑ i, (W v).w i) + n * m v)) Up hUp w₀ hw₀ hu
    J (χ.comp θ) hJo hJc hφ
  exact ⟨⟨π, rfl, W, hW, m, hm, _, rfl, J, χ.comp θ, hcusp, htf, S, Kw, Φ, κ, hw₀, a1, a2, a3, a4, a5, a6, a7, a8⟩⟩

theorem wtOf_of (h0 : WtCore) : WtOf := by
  intro E _ _ _ A n p _ S x U w₀ Up V thQ hth B y hdeg hsep
  let y₀ : GL (Fin n) E × ℚˣ := y.1
  let β : GL (Fin n) E := B.β
  have hc : ∀ z : E, S.L.e.symm z = z := fun z => S.L.e.symm_apply_eq.2 (S.L_e z).symm
  have hmin : minpoly E y₀.1.val = y₀.1.val.charpoly := by
    refine Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic (Matrix.isIntegral _)) (Matrix.charpoly_monic _)
      (Matrix.minpoly_dvd_charpoly _) ?_ |>.symm
    rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
    exact hdeg.ge
  let Hc : Matrix (Fin n) (Fin n) E := (A.H n).map (IsCMField.complexConj E : E →+* E)
  have hu : IsUnit Hc.det := by
    rw [show Hc.det = _ from ((IsCMField.complexConj E : E →+* E).map_det _).symm]
    exact ((map_ne_zero _).2 (A.det_ne n)).isUnit
  have hy : y₀.1.val * β.val * (Hc⁻¹ * (y₀.1.val.map (IsCMField.complexConj E : E →+* E))ᵀ * Hc) = algebraMap ℚ _ (y₀.2 : ℚ) * β.val := y.2.1
  have hrel : (y₀.1.val.map (IsCMField.complexConj E))ᵀ * ((Matrix.isUnit_iff_isUnit_det _).2 hu).unit.val * β⁻¹.val * y₀.1.val =
      ((y₀.2 : ℚ) : E) • (((Matrix.isUnit_iff_isUnit_det _).2 hu).unit.val * β⁻¹.val) := by
    rw [IsUnit.unit_spec]
    have e1 : (y₀.1.val.map (IsCMField.complexConj E))ᵀ * Hc = ((y₀.2 : ℚ) : E) • (Hc * β⁻¹.val * y₀.1⁻¹.val * β.val) := by
      have h2 := congrArg (fun M => Hc * β⁻¹.val * y₀.1⁻¹.val * M) hy
      simp only [Matrix.mul_assoc, Units.inv_mul_cancel_left, Matrix.mul_nonsing_inv_cancel_left _ _ hu] at h2
      rw [← Algebra.smul_def, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_smul] at h2
      simp only [Matrix.mul_assoc]
      rw [Rat.cast_smul_eq_qsmul]
      exact h2
    rw [e1]
    simp only [smul_mul_assoc, Matrix.mul_assoc, Units.mul_inv_cancel_left, Units.inv_mul, Matrix.mul_one]
  have hsep' : y₀.1.val.charpoly.Separable := hmin ▸ hsep
  have key := h0 E n V.W V.m V.pos y₀.1 (((Matrix.isUnit_iff_isUnit_det _).2 hu).unit * β⁻¹) (thQ y₀).1 y₀.2
    (by rw [Units.val_mul, ← Matrix.mul_assoc]; exact hrel) hsep' (hth y₀).1
  have e2 : thQ y₀ = ((thQ y₀).1, y₀.2⁻¹) := Prod.ext rfl (hth y₀).2
  have e3 : LocalSmoothExtension.endPol S.L (minpoly E y₀.1.val) = LocalSmoothExtension.invPol y₀.1.val.charpoly := by
    unfold LocalSmoothExtension.endPol
    rw [hmin]
    refine congrArg LocalSmoothExtension.invPol (Polynomial.ext fun i => ?_)
    exact (Polynomial.coeff_map _ _).trans (hc _)
  rw [← V.jz_eq, ← e2, ← e3] at key
  exact key

theorem expOf_of (h0 : ExpCore) (h1 : AutEx) (h2 : WtAt) (h3 : EpsIff) : ExpOf := by
  intro E _ _ _ A n p _ S x U w₀ Up V d hd hx hG
  obtain ⟨a1, a2⟩ := h0 E n d x hd hx V.W V.m V.pos
  refine ⟨a1, fun τ => ?_⟩
  obtain ⟨σ, hσ⟩ := h1 E τ A.τ₀
  refine ⟨σ, hσ, fun lam hl j hj => ?_⟩
  obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hj
  have e : lam = V.W.at τ := (h2 E n S.facts.pos V.π).2 V.W V.hW τ lam (by rw [V.hV]; exact hl)
  subst e
  rw [V.jz_eq]
  refine a2 τ A.τ₀ σ hσ _ (fun φ => ?_) k
  have e1 : (starRingEnd ℂ) (A.τ₀ (A.ω : E)) = σ ((starRingEnd ℂ) (τ (A.ω : E))) := by
    rw [← IsCMField.complexEmbedding_complexConj, ← IsCMField.complexEmbedding_complexConj, hσ]
  have e2 : (σ (φ (A.ω : E)) = (starRingEnd ℂ) (A.τ₀ (A.ω : E))) ↔ φ x = -τ x := by
    rw [e1, σ.injective.eq_iff]
    exact h3 E d x A.ω hd hx hG.1 hG.2 τ φ
  exact if_congr e2 rfl rfl

end UpperTheory.Gal.Int.Geo.Pl

end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PCharConj

section

section

open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions UpperTheory.Gal.CertificateRingHomMap
open scoped Classical

theorem UpperTheory.Gal.CertificateRingHomMap.pCharConj_of :
    UpperTheory.Gal.CertificateRingHomMap.CharConj := by
  intro E _ _ _ n y P s h φ t ht
  set A : Matrix (Fin n) (Fin n) ℂ := (y : Matrix (Fin n) (Fin n) E).map φ with hAdef
  set Q : Matrix (Fin n) (Fin n) ℂ := (P : Matrix (Fin n) (Fin n) E).map φ with hQdef
  set B : Matrix (Fin n) (Fin n) ℂ :=
    (y : Matrix (Fin n) (Fin n) E).map (NumberField.ComplexEmbedding.conjugate φ) with hBdef
  have hB : B = ((y : Matrix (Fin n) (Fin n) E).map (IsCMField.complexConj E)).map φ := by
    ext i j
    simp only [B, Matrix.map_apply]
    rw [NumberField.ComplexEmbedding.conjugate_coe_eq,
      NumberField.IsCMField.complexEmbedding_complexConj]
  have hrel : Bᵀ * Q * A = ((s : ℚ) : ℂ) • Q := by
    have h2 := congrArg (fun M : Matrix (Fin n) (Fin n) E => M.map φ) h
    simp only [Matrix.map_mul] at h2
    rw [Matrix.transpose_map] at h2
    rw [hB, hQdef, hAdef, h2]
    ext i j
    simp [Matrix.map_apply]
  have hA : ((y : Matrix (Fin n) (Fin n) E).map φ).charpoly = ∏ i, (X - C (t i)) := by
    rw [Matrix.charpoly_map]; exact ht
  have hdetA : A.det ≠ 0 := by
    have hu : IsUnit (y : Matrix (Fin n) (Fin n) E).det :=
      (Matrix.isUnit_iff_isUnit_det _).mp y.isUnit
    rw [hAdef, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero φ).mpr hu.ne_zero
  have hdetQ : Q.det ≠ 0 := by
    have hu : IsUnit (P : Matrix (Fin n) (Fin n) E).det :=
      (Matrix.isUnit_iff_isUnit_det _).mp P.isUnit
    rw [hQdef, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero φ).mpr hu.ne_zero
  have hprodt : A.det = ∏ i, t i := by
    have e := congrArg (Polynomial.eval 0) hA
    rw [Matrix.eval_charpoly, Polynomial.eval_prod] at e
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, zero_sub] at e
    rw [map_zero, zero_sub, Matrix.det_neg, Fintype.card_fin] at e
    have e2 : ∏ i, -t i = (-1) ^ n * ∏ i, t i := by
      calc ∏ i, -t i = ∏ i, ((-1) * t i) := by simp
        _ = (-1) ^ n * ∏ i, t i := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [e2] at e
    exact mul_left_cancel₀ (pow_ne_zero n (neg_ne_zero.mpr one_ne_zero)) e
  have ht0 : ∀ i, t i ≠ 0 := by
    intro i hi
    apply hdetA
    rw [hprodt]
    exact Finset.prod_eq_zero (Finset.mem_univ i) hi
  have hpt : ∏ i, t i ≠ 0 := hprodt ▸ hdetA
  refine ⟨ht0, ?_⟩
  rw [← Matrix.charpoly_map]
  apply Polynomial.eq_of_infinite_eval_eq
  apply Set.Infinite.mono (s := {z : ℂ | z ≠ 0})
  · intro z hz
    simp only [Set.mem_setOf_eq] at hz ⊢
    have key : (Matrix.scalar (Fin n) z - B).det * A.det =
        z ^ n * (-1) ^ n * (Matrix.scalar (Fin n) (((s : ℚ) : ℂ) / z) - A).det := by
      have e1 : (Matrix.scalar (Fin n) z - Bᵀ) * Q * A = Q * (z • A - ((s : ℚ) : ℂ) • 1) := by
        rw [Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, sub_mul, sub_mul, hrel, mul_sub]
        simp [smul_mul_assoc, mul_smul_comm]
      have e2 : (Matrix.scalar (Fin n) z - B).det = (Matrix.scalar (Fin n) z - Bᵀ).det := by
        rw [← Matrix.eval_charpoly, ← Matrix.eval_charpoly, Matrix.charpoly_transpose]
      have e3 : z • A - ((s : ℚ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) =
          z • (-(Matrix.scalar (Fin n) (((s : ℚ) : ℂ) / z) - A)) := by
        rw [neg_sub, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, smul_sub, smul_smul,
          mul_div_cancel₀ _ hz]
      have e4 := congrArg Matrix.det e1
      rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, e3, Matrix.det_smul, Matrix.det_neg,
        Fintype.card_fin, ← e2] at e4
      apply mul_left_cancel₀ hdetQ
      linear_combination e4
    have hAev := congrArg (Polynomial.eval (((s : ℚ) : ℂ) / z)) hA
    rw [Matrix.eval_charpoly, Polynomial.eval_prod] at hAev
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at hAev
    rw [hAev, hprodt] at key
    rw [Matrix.eval_charpoly, Polynomial.eval_prod]
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    have hfac : ∀ i, (z - ((s : ℚ) : ℂ) / t i) * t i = (z * -1) * (((s : ℚ) : ℂ) / z - t i) := by
      intro i
      field_simp [ht0 i, hz]
      ring
    have hq : (∏ i, (z - ((s : ℚ) : ℂ) / t i)) * ∏ i, t i =
        z ^ n * (-1) ^ n * ∏ i, (((s : ℚ) : ℂ) / z - t i) := by
      rw [← Finset.prod_mul_distrib, Finset.prod_congr rfl (fun i _ => hfac i),
        Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_pow]
    exact mul_right_cancel₀ hpt (key.trans hq.symm)
  · exact (Set.finite_singleton (0 : ℂ)).infinite_compl
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PSchHom

section

section

open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions UpperTheory.Gal.CertificateRingHomMap
open scoped Classical

theorem UpperTheory.Gal.CertificateRingHomMap.pSchHom_of :
    UpperTheory.Gal.CertificateRingHomMap.SchHom := by
  intro n t _
  refine ⟨fun lam c _ => UpperTheory.Gal.Schur.SchurHomog_holds ℂ n lam t c, fun m => ?_⟩
  obtain ⟨h0, h1⟩ := UpperTheory.Gal.Schur.SchurDet_holds ℂ n t
  have h := h1 (fun _ => 0) m
  simp only [zero_add] at h
  rw [h, h0, mul_one]
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PTrRho

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions UpperTheory.Gal.CertificateRingHomMap
open scoped Classical

theorem UpperTheory.Gal.CertificateRingHomMap.pTrRho_of :
    UpperTheory.Gal.CertificateRingHomMap.TrRho := by
  intro E _ _ _ n W g
  set e := GlobalTheory.BCT.TrKer.wspEquivVV W
  set F : GlobalTheory.BCT.TrKer.Wsp W →ₗ[ℂ] GlobalTheory.BCT.TrKer.Wsp W :=
    PiTensorProduct.map (fun v => GlobalTheory.Branching.sqRep ℂ n (W v) (g v)) with hF
  have hcomp : Formalism.L2.DIV.rhoK W g ∘ₗ (e : GlobalTheory.BCT.TrKer.Wsp W →ₗ[ℂ] _) =
      (e : GlobalTheory.BCT.TrKer.Wsp W →ₗ[ℂ] _) ∘ₗ F := by
    apply PiTensorProduct.ext
    refine MultilinearMap.ext (fun u => ?_)
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, hF, PiTensorProduct.map_tprod]
    dsimp only [e, GlobalTheory.BCT.TrKer.wspEquivVV, LinearEquiv.ofLinear_apply]
    show Formalism.L2.DIV.rhoK W g (GlobalTheory.BCT.TrKer.wspToVV W (PiTensorProduct.tprod ℂ u)) =
      GlobalTheory.BCT.TrKer.wspToVV W (PiTensorProduct.tprod ℂ _)
    rw [GlobalTheory.BCT.TrKer.wspToVV_tprod, GlobalTheory.BCT.TrKer.wspToVV_tprod, rhoK_tenMul]
  have hconj : Formalism.L2.DIV.rhoK W g = e.conj F := by
    rw [LinearEquiv.conj_apply, ← hcomp]
    refine LinearMap.ext (fun x => ?_)
    simp
  rw [hconj, LinearMap.trace_conj', hF, GlobalTheory.BCT.TrKer.trace_piMap]
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PWtAtOf

section

section

open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions UpperTheory.Gal.CertificateRingHomMap
open scoped Classical

theorem UpperTheory.Gal.CertificateRingHomMap.pWtAt_of :
    UpperTheory.Gal.CertificateRingHomMap.WtAt := by
  intro E _ _ _ n _ π
  refine ⟨⟨(AU.mk π).wt, AutSub.finPart_wt_ne_bot E n π⟩, fun W hW τ lam hlam => ?_⟩
  obtain ⟨f, hf, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
  have hT :=
    GlobalTheory.Cong.ofType_of_finPart_fixed E n π W ⊥ f hf hf0 (by
      intro k hk v g
      rw [Subgroup.mem_bot.1 hk, mul_one])
  exact hasWeightAt_unique π τ hlam (hT.wt τ)
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.CharConjHolds

section

@[expose] public section

namespace UpperTheory.Gal.CertificateRingHomMap

theorem trRho_holds : TrRho := pTrRho_of
theorem trSch_holds : TrSch := pTrSch_of
theorem schHom_holds : SchHom := pSchHom_of
theorem charConj_holds : CharConj := pCharConj_of
theorem wtCore_holds : WtCore := pWtCore_of trRho_holds trSch_holds schHom_holds charConj_holds
theorem autEx_holds : AutEx := pAutEx_of
theorem wtAt_holds : WtAt := pWtAt_of
theorem epsIff_holds : EpsIff := pEpsIff_of
theorem expSum_holds : ExpSum := pExpSum_of
theorem expCore_holds : ExpCore := pExpCore_of expSum_holds

end UpperTheory.Gal.CertificateRingHomMap

namespace UpperTheory.Gal.Int.Geo.Pl

theorem vecEx_holds : VecEx := vecEx_of CertificateRingHomMap.seedGU_holds CertificateRingHomMap.wtAt_holds

theorem wtOf_holds : WtOf := wtOf_of CertificateRingHomMap.wtCore_holds

theorem expOf_holds : ExpOf := expOf_of CertificateRingHomMap.expCore_holds CertificateRingHomMap.autEx_holds CertificateRingHomMap.wtAt_holds CertificateRingHomMap.epsIff_holds

end UpperTheory.Gal.Int.Geo.Pl
end
end
