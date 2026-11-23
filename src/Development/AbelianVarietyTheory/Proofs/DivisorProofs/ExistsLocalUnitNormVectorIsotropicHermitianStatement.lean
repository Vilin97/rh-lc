module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitNormOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonHermitianGramDetTwoVectorsNeStatement
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.IsHermHyperbolic
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsIsotropicBasisNonorthogonalTwoVectors
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HermitianFormFiniteZerosOnLineCmExt
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitNormOne
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HermitianFormFiniteZerosOnLineCmExt

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitNormGramDetPairFieldCase

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published GlobalTheory.PlaneNorm
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.PlaneNorm.FieldCase

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E] (K : Type) [Field K] [Algebra F K]

theorem sigR_inclR (σ : E →ₐ[F] E) (e : E) : sigR K σ (inclR K e) = inclR K (σ e) := rfl

theorem sigR_sigR (σ : E →ₐ[F] E) (hσ : ∀ e, σ (σ e) = e) (x : K ⊗[F] E) :
    sigR K σ (sigR K σ x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul k e => simp [sigR, hσ]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem inclR_injective : Function.Injective (inclR (F := F) (E := E) K) :=
  Algebra.TensorProduct.includeRight_injective (algebraMap F K).injective

theorem hR_eq_hf (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (x y : Fin M → K ⊗[F] E) :
    hR K σ J x y = GlobalTheory.UTrans.hf (sigR K σ) (JR K J).transpose y x := by
  simp only [hR, Formalism.UG.hform, GlobalTheory.UTrans.hf, Matrix.transpose_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

end Alg

theorem exists_unitNorm_pair : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (K : Type) [Field K] [Algebra F K] (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → (∀ a : K ⊗[F] E, a ≠ 0 → IsUnit a) → (∃ u : Fin M → K ⊗[F] E, u ≠ 0 ∧ hR K σ J u u = 0) → ∀ a b : Fin M → K ⊗[F] E, a ≠ 0 → b ≠ 0 → ∃ w : Fin M → K ⊗[F] E, IsUnitNorm K σ (-(gram2R K σ J a w)) ∧ IsUnitNorm K σ (-(gram2R K σ J w b)) := by
  intro F E _ _ _ _ _ σ hcm K _ _ M J hJ hunit hiso a b ha hb
  have hinj := inclR_injective (F := F) (E := E) K
  haveI : Nontrivial (K ⊗[F] E) := hinj.nontrivial
  haveI : CharZero (K ⊗[F] E) := charZero_of_injective_algebraMap (algebraMap F (K ⊗[F] E)).injective
  have hfield : IsField (K ⊗[F] E) :=
    ⟨exists_pair_ne _, mul_comm, fun {x} hx => (hunit x hx).exists_right_inv⟩
  letI : Field (K ⊗[F] E) := hfield.toField
  have hG : GlobalTheory.UTrans.IsHerm (sigR K σ) (JR K J).transpose :=
    { invol := sigR_sigR K σ (GlobalTheory.HermLineZeros.conj_invol hcm)
      ne_id := by
        obtain ⟨d, hd⟩ := GlobalTheory.HermLineZeros.exists_conj_ne hcm
        exact ⟨inclR K d, fun h => hd (hinj (by rw [← sigR_inclR]; exact h))⟩
      herm := fun p q => by
        simp only [Matrix.transpose_apply, JR, Matrix.map_apply, sigR_inclR]
        rw [hJ.1 p q]
      det_ne := by
        rw [Matrix.det_transpose, JR, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
        intro h
        exact hJ.2 (hinj (by rw [h, map_zero])) }
  have hsymm : ∀ x y, sigR K σ (hR K σ J x y) = hR K σ J y x := by
    intro x y
    rw [hR_eq_hf, hR_eq_hf, GlobalTheory.UTrans.IsoBasis.hf_symm hG]
  obtain ⟨u, hu0, huu⟩ := hiso
  have hz : ∃ z, z ≠ 0 ∧ GlobalTheory.UTrans.hf (sigR K σ) (JR K J).transpose z z = 0 := ⟨u, hu0, by rw [← hR_eq_hf]; exact huu⟩
  obtain ⟨e, he, hne⟩ := GlobalTheory.UTrans.IsoBasis.exists_isotropic_avoid hG hz
    ![GlobalTheory.UTrans.IsoBasis.hfL (sigR K σ) (JR K J).transpose a, GlobalTheory.UTrans.IsoBasis.hfL (sigR K σ) (JR K J).transpose b] (by
      intro i
      fin_cases i
      · exact GlobalTheory.UTrans.IsoBasis.hfL_ne hG ha
      · exact GlobalTheory.UTrans.IsoBasis.hfL_ne hG hb)
  have hee : hR K σ J e e = 0 := by rw [hR_eq_hf]; exact he
  have h1 : hR K σ J a e ≠ 0 := by
    rw [hR_eq_hf]; exact hne 0
  have h2 : hR K σ J e b ≠ 0 := by
    intro h
    apply hne 1
    change GlobalTheory.UTrans.hf (sigR K σ) (JR K J).transpose e b = 0
    rw [← hR_eq_hf, ← hsymm, h, map_zero]
  refine ⟨e, ⟨hR K σ J a e, isUnit_iff_ne_zero.2 h1, ?_⟩, ⟨hR K σ J e b, isUnit_iff_ne_zero.2 h2, ?_⟩⟩
  · rw [hsymm, gram2R, hee]; ring
  · rw [hsymm, gram2R, hee]; ring

end GlobalTheory.PlaneNorm.FieldCase
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitNormGramDetPairFieldCaseStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published GlobalTheory.PlaneNorm
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_unitNorm_gramDet_pair_fieldCase : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (K : Type) [Field K] [Algebra F K] (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → (∀ a : K ⊗[F] E, a ≠ 0 → IsUnit a) → (∃ u : Fin M → K ⊗[F] E, u ≠ 0 ∧ hR K σ J u u = 0) → ∀ a b : Fin M → K ⊗[F] E, a ≠ 0 → b ≠ 0 → ∃ w : Fin M → K ⊗[F] E, IsUnitNorm K σ (-(gram2R K σ J a w)) ∧ IsUnitNorm K σ (-(gram2R K σ J w b)) := by
  first | exact @GlobalTheory.PlaneNorm.FieldCase.exists_unitNorm_pair | exact GlobalTheory.PlaneNorm.FieldCase.exists_unitNorm_pair | (intros; apply GlobalTheory.PlaneNorm.FieldCase.exists_unitNorm_pair <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorCMIsFieldOrNormSurjective

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published GlobalTheory.PlaneNorm
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.NormDichotomy

theorem unit_or_norm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (K : Type) [Field K] [Algebra F K], (∀ a : K ⊗[F] E, a ≠ 0 → IsUnit a) ∨ (∀ k : K, k ≠ 0 → ∃ t : K ⊗[F] E, t * sigR K σ t = algebraMap K (K ⊗[F] E) k) := by
  intro F E _ _ _ _ _ σ h K _ _

  obtain ⟨e, he⟩ := GlobalTheory.HermLineZeros.exists_conj_ne h
  set d : E := e - σ e with hd
  have hσd : σ d = -d := by
    rw [hd, map_sub, GlobalTheory.HermLineZeros.conj_invol h]; ring
  have hd0 : d ≠ 0 := by
    intro h0; apply he; rw [hd, sub_eq_zero] at h0; exact h0.symm
  have hfix : σ (d * d) = d * d := by rw [map_mul, hσd]; ring
  obtain ⟨c0, hc0⟩ := GlobalTheory.HermLineZeros.exists_of_fixed h _ hfix
  haveI : CharZero F := inferInstance
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap F K).injective
  set L := K ⊗[F] E
  set ι := algebraMap K L with hι
  set D : L := inclR K d with hD
  set c : K := algebraMap F K c0 with hc
  have hc0ne : c0 ≠ 0 := by
    rintro rfl; apply hd0; rw [map_zero] at hc0; exact mul_self_eq_zero.1 hc0.symm
  have hcne : c ≠ 0 := by rw [hc]; exact (map_ne_zero _).2 hc0ne
  have hDD : D * D = ι c := by
    rw [hD, ← map_mul, ← hc0, hc, hι, ← IsScalarTower.algebraMap_apply]
    exact (Algebra.TensorProduct.includeRight : E →ₐ[F] K ⊗[F] E).commutes c0
  have hsD : sigR K σ D = -D := by
    show inclR K (σ d) = _
    rw [hσd, map_neg]
  have hst : ∀ t : K, sigR K σ (ι t) = ι t := by
    intro t
    show t ⊗ₜ[F] σ 1 = _
    rw [map_one]
    rfl

  have hli : LinearIndependent F ![(1 : E), d] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst0
    rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hst0
    have e2 := congrArg σ hst0
    rw [map_add (f := _), map_mul, AlgHom.commutes, AlgHom.commutes, hσd, map_zero] at e2
    have ht : algebraMap F E t * d = 0 := by linear_combination (hst0 - e2) / 2
    have ht0 : t = 0 := by
      rcases mul_eq_zero.1 ht with h1 | h1
      · exact (map_eq_zero _).1 h1
      · exact absurd h1 hd0
    refine ⟨?_, ht0⟩
    rw [ht0, map_zero, zero_mul, add_zero] at hst0
    exact (map_eq_zero _).1 hst0
  have hcard : Fintype.card (Fin 2) = Module.finrank F E := by rw [h.2.2.1]; rfl
  let b := basisOfLinearIndependentOfCardEqFinrank hli hcard
  let bK := Algebra.TensorProduct.basis K b
  have hdec : ∀ a : L, ∃ u v : K, a = ι u + ι v * D := by
    intro a
    refine ⟨bK.repr a 0, bK.repr a 1, ?_⟩
    conv_lhs => rw [← bK.sum_repr a]
    rw [Fin.sum_univ_two]
    have hb : ⇑b = ![(1 : E), d] := coe_basisOfLinearIndependentOfCardEqFinrank _ _
    have h0 : bK 0 = 1 := by
      simp only [bK, Algebra.TensorProduct.basis_apply, hb, Matrix.cons_val_zero]; rfl
    have h1 : bK 1 = D := by
      simp only [bK, Algebra.TensorProduct.basis_apply, hb, Matrix.cons_val_one, Matrix.head_cons]; rfl
    rw [h0, h1, Algebra.smul_def, Algebra.smul_def, mul_one]
  by_cases hsq : ∃ r : K, r * r = c
  · right
    obtain ⟨r, hr⟩ := hsq
    have hr0 : r ≠ 0 := by rintro rfl; exact hcne (by rw [← hr, mul_zero])
    have h2 : ι (1 / 2) * 2 = 1 := by
      rw [show (2 : L) = ι 2 from (map_ofNat ι 2).symm, ← map_mul]; norm_num
    have hs : ι r * ι r⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ hr0, map_one]
    have hD2 : D * D = ι r * ι r := by rw [hDD, ← hr, map_mul]
    set ε : L := ι (1 / 2) * (1 + ι r⁻¹ * D) with hε
    have he0 : ε * (1 - ε) = 0 := by
      rw [hε]
      linear_combination (-(1 + ι r⁻¹ * D) * ι (1 / 2)) * h2 + (-ι (1 / 2) ^ 2 * ι r⁻¹ ^ 2) * hD2 + (-ι (1 / 2) ^ 2 * (ι r⁻¹ * ι r + 1)) * hs
    have hσε : sigR K σ ε = 1 - ε := by
      rw [hε, map_mul, map_add (f := _), map_mul, map_one, hst, hst, hsD]
      linear_combination h2
    intro k _
    refine ⟨ι k * ε + (1 - ε), ?_⟩
    rw [map_add (f := _), map_mul, map_sub, map_one, hst, hσε]
    linear_combination (ι k ^ 2 + 1 - 2 * ι k) * he0
  · left
    push_neg at hsq
    intro a ha
    obtain ⟨u, v, rfl⟩ := hdec a
    have hn : u * u - c * (v * v) ≠ 0 := by
      intro h0
      by_cases hv : v = 0
      · apply ha
        have : u * u = 0 := by rw [hv] at h0; simpa using h0
        rw [mul_self_eq_zero.1 this, hv, map_zero, zero_mul, add_zero]
      · apply hsq (u / v)
        field_simp
        linear_combination h0
    have hN : (ι u + ι v * D) * sigR K σ (ι u + ι v * D) = ι (u * u - c * (v * v)) := by
      rw [map_add (f := _), map_mul, hst, hst, hsD, map_sub, map_mul, map_mul, map_mul]
      linear_combination (-(ι v * ι v)) * hDD
    refine IsUnit.of_mul_eq_one (sigR K σ (ι u + ι v * D) * ι (u * u - c * (v * v))⁻¹) ?_
    rw [← mul_assoc, hN, ← map_mul, mul_inv_cancel₀ hn, map_one]

end GlobalTheory.NormDichotomy
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorCMIsFieldOrNormSurjectiveStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published GlobalTheory.PlaneNorm
open scoped TensorProduct

theorem _root_.GlobalTheory.T.tensorCM_isField_or_norm_surjective : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (K : Type) [Field K] [Algebra F K], (∀ a : K ⊗[F] E, a ≠ 0 → IsUnit a) ∨ (∀ k : K, k ≠ 0 → ∃ t : K ⊗[F] E, t * sigR K σ t = algebraMap K (K ⊗[F] E) k) := by
  first | exact @GlobalTheory.NormDichotomy.unit_or_norm | exact GlobalTheory.NormDichotomy.unit_or_norm | (intros; apply GlobalTheory.NormDichotomy.unit_or_norm <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalUnitNormVectorIsotropicHermitian

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published GlobalTheory.PlaneNorm
open scoped TensorProduct

namespace GlobalTheory.PlaneNorm

theorem exists_local_unitNorm_vector : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (K : Type) [Field K] [Algebra F K] (M : ℕ) (J : Matrix (Fin M) (Fin M) E), 2 ≤ M → IsHermND σ J → (∃ u : Fin M → K ⊗[F] E, u ≠ 0 ∧ hR K σ J u u = 0) → ∀ x y : Fin M → E, hE σ J x x ≠ 0 → hE σ J y y ≠ 0 → ∃ w : Fin M → K ⊗[F] E, IsUnitNorm K σ (-(gram2R K σ J (fun i => inclR K (x i)) w)) ∧ IsUnitNorm K σ (-(gram2R K σ J w (fun i => inclR K (y i)))) := by
  intro F E _ _ _ _ _ σ hcm K _ _ M J hM hJ hiso x y hx hy
  have hinj : Function.Injective (inclR (F := F) K : E →+* K ⊗[F] E) := Algebra.TensorProduct.includeRight_injective (algebraMap F K).injective
  have hne : ∀ z : Fin M → E, hE σ J z z ≠ 0 → ((fun i => inclR K (z i)) : Fin M → K ⊗[F] E) ≠ 0 := by
    intro z hz h0
    apply hz
    have hz0 : z = 0 := funext fun i => hinj (by simpa using congrFun h0 i)
    subst hz0
    simp [hE, Formalism.UG.hform]
  rcases GlobalTheory.T.tensorCM_isField_or_norm_surjective F E σ hcm K with hfld | hspl
  · exact GlobalTheory.T.exists_unitNorm_gramDet_pair_fieldCase F E σ hcm K M J hJ hfld hiso _ _ (hne x hx) (hne y hy)
  · obtain ⟨w, hxw, hwy⟩ := GlobalTheory.T.exists_common_hermitianGramDetTwoVectors_ne F E σ hcm M J hM hJ x y hx hy
    have hs : ∀ e : E, sigR K σ (inclR K e) = inclR K (σ e) := fun e => rfl
    have hRE : ∀ a b : Fin M → E, hR K σ J (fun i => inclR K (a i)) (fun i => inclR K (b i)) =
        inclR K (hE σ J a b) := by
      intro a b

      simp only [hR, hE, Formalism.UG.hform, map_sum, map_mul, hs, JR, Matrix.map_apply, RingHom.coe_coe]
    have hG : ∀ a b : Fin M → E, gram2R K σ J (fun i => inclR K (a i)) (fun i => inclR K (b i)) =
        inclR K (gram2E σ J a b) := by
      intro a b
      simp only [gram2R, gram2E, hRE, map_sub, map_mul]
    have hsym : ∀ a b : Fin M → E, σ (hE σ J a b) = hE σ J b a := by
      intro a b

      simp only [hE, Formalism.UG.hform, map_sum, map_mul, RingHom.coe_coe, GlobalTheory.HermLineZeros.conj_invol hcm]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [hJ.1]
      ring
    have hfix : ∀ a b : Fin M → E, σ (gram2E σ J a b) = gram2E σ J a b := by
      intro a b
      simp only [gram2E, map_sub, map_mul, hsym]
      ring
    have key : ∀ a b : Fin M → E, gram2E σ J a b ≠ 0 →
        IsUnitNorm K σ (-(gram2R K σ J (fun i => inclR K (a i)) (fun i => inclR K (b i)))) := by
      intro a b hab
      obtain ⟨g, hg⟩ := GlobalTheory.HermLineZeros.exists_of_fixed hcm _ (hfix a b)
      have hg0 : g ≠ 0 := by rintro rfl; exact hab (by rw [← hg, map_zero])
      have hk : algebraMap F K (-g) ≠ 0 := by
        rw [map_neg, neg_ne_zero, ne_eq, map_eq_zero_iff _ (algebraMap F K).injective]; exact hg0
      obtain ⟨t, ht⟩ := hspl _ hk
      have hval : -(gram2R K σ J (fun i => inclR K (a i)) (fun i => inclR K (b i))) =
          algebraMap K (K ⊗[F] E) (algebraMap F K (-g)) := by
        rw [hG, ← hg, map_neg, map_neg]
        congr 1
        rw [← IsScalarTower.algebraMap_apply]
        exact (Algebra.TensorProduct.includeRight : E →ₐ[F] K ⊗[F] E).commutes g
      have hu : IsUnit (t * sigR K σ t) := by
        rw [ht]; exact (IsUnit.mk0 _ hk).map _
      exact ⟨t, isUnit_of_mul_isUnit_left hu, by rw [ht, hval]⟩
    exact ⟨fun i => inclR K (w i), key x w hxw, key w y hwy⟩

end GlobalTheory.PlaneNorm
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalUnitNormVectorIsotropicHermitianStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published GlobalTheory.PlaneNorm
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_local_unitNorm_vector_isotropic_hermitian : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (K : Type) [Field K] [Algebra F K] (M : ℕ) (J : Matrix (Fin M) (Fin M) E), 2 ≤ M → IsHermND σ J → (∃ u : Fin M → K ⊗[F] E, u ≠ 0 ∧ hR K σ J u u = 0) → ∀ x y : Fin M → E, hE σ J x x ≠ 0 → hE σ J y y ≠ 0 → ∃ w : Fin M → K ⊗[F] E, IsUnitNorm K σ (-(gram2R K σ J (fun i => inclR K (x i)) w)) ∧ IsUnitNorm K σ (-(gram2R K σ J w (fun i => inclR K (y i)))) := by
  first | exact @GlobalTheory.PlaneNorm.exists_local_unitNorm_vector | exact GlobalTheory.PlaneNorm.exists_local_unitNorm_vector | (intros; apply GlobalTheory.PlaneNorm.exists_local_unitNorm_vector <;> assumption)
end
end
