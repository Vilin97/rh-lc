module

public import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
public import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoeffHeckeTOperatorQExpansionSlashSumStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoeffHeckeVOperatorPolynomialGrowthQExpansionStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeCharacterSlashSumIndepRepsStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
public import Mathlib.Data.Nat.Prime.Int
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsLeftGamma0CosetDecompositionHeckeRepTOperatorStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlashIntMatrixPosDetPropertiesStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsLeftGamma0CosetDecompositionHeckeRepLowerLevel

section

@[expose] public section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

lemma repL_det (L q : ℕ) (i : Option (Fin q)) : (repL L q i).det = q := by
  cases i <;> simp [repL, Matrix.det_fin_two_of]

lemma gamma0_lower_dvd {L : ℕ} (γ : Gamma0 L) : (L : ℤ) ∣ ((γ : SL(2, ℤ)) : M2) 1 0 := by
  have := Gamma0_mem.mp γ.2
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (by exact_mod_cast this)

lemma exists_kernel_param {K : Type*} [Field K] (a b c d l : K) (hl : l ≠ 0)
    (hdet : a * d - b * c = 0) (hbd : b ≠ 0 ∨ d ≠ 0) : ∃ u, a = l * u * b ∧ c = l * u * d := by
  by_cases hd : d = 0
  · have hb : b ≠ 0 := hbd.resolve_right (by simpa using hd)
    refine ⟨a / (l * b), by field_simp, ?_⟩
    subst hd
    have : b * c = 0 := by linear_combination -hdet
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hb
    · simp [h]
  · refine ⟨c / (l * d), ?_, by field_simp⟩
    field_simp
    linear_combination hdet

theorem repL_LRep : ∀ L q : ℕ, q.Prime → ¬ q ∣ L → LRep L (DT L q) (repL L q) := by
  intro L q hq hqL
  have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne_zero
  have hqZ : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq
  have hqLZ : ¬ (q : ℤ) ∣ L := by exact_mod_cast hqL
  haveI := Fact.mk hq
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨γ, i⟩ -
    refine ⟨?_, ?_⟩
    · simp [Matrix.det_mul, repL_det]
    · have h := gamma0_lower_dvd γ
      cases i with
      | none => simpa [repL, Matrix.mul_apply, Fin.sum_univ_two] using h
      | some j =>
        simp only [repL, Matrix.mul_apply, Fin.sum_univ_two]
        simp
        exact dvd_add (dvd_mul_of_dvd_left h _) (Dvd.dvd.mul_left (dvd_mul_right _ _) _)
  · rintro ⟨γ, i⟩ - ⟨γ', i'⟩ - h
    dsimp only at h
    have hd := (γ : SL(2, ℤ)).2
    have hd' := (γ' : SL(2, ℤ)).2
    rw [Matrix.det_fin_two] at hd hd'
    have e00 := congrFun (congrFun h 0) 0
    have e01 := congrFun (congrFun h 0) 1
    have e10 := congrFun (congrFun h 1) 0
    have e11 := congrFun (congrFun h 1) 1
    have hq0' : q ≠ 0 := hq.ne_zero
    have hq1 : ¬ (q : ℤ) ∣ 1 := hqZ.not_dvd_one
    rcases i with _ | j <;> rcases i' with _ | j' <;>
      simp [repL, Matrix.mul_apply, Fin.sum_univ_two, hq0'] at e00 e01 e10 e11
    · refine Prod.ext (Subtype.ext (Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_)) rfl
      fin_cases i <;> fin_cases j <;> simp <;> assumption
    · exact absurd (Dvd.intro (((γ' : SL(2, ℤ)) : M2) 0 0 * ((γ : SL(2, ℤ)) : M2) 1 1 -
          ((γ : SL(2, ℤ)) : M2) 0 1 * ((γ' : SL(2, ℤ)) : M2) 1 0)
        (by linear_combination hd' + ((γ' : SL(2, ℤ)) : M2) 0 0 * e11 - ((γ' : SL(2, ℤ)) : M2) 1 0 * e01)) hq1
    · exact absurd (Dvd.intro (((γ : SL(2, ℤ)) : M2) 0 0 * ((γ' : SL(2, ℤ)) : M2) 1 1 -
          ((γ' : SL(2, ℤ)) : M2) 0 1 * ((γ : SL(2, ℤ)) : M2) 1 0)
        (by linear_combination hd - ((γ : SL(2, ℤ)) : M2) 0 0 * e11 + ((γ : SL(2, ℤ)) : M2) 1 0 * e01)) hq1
    · have h0 : (q : ℤ) ∣ (L : ℤ) * ((j : ℕ) - (j' : ℕ) : ℤ) * ((γ : SL(2, ℤ)) : M2) 0 1 :=
        Dvd.intro (((γ' : SL(2, ℤ)) : M2) 0 0 - ((γ : SL(2, ℤ)) : M2) 0 0)
          (by linear_combination -e00 + ((L : ℤ) * ((j' : ℕ) : ℤ)) * e01)
      have h1 : (q : ℤ) ∣ (L : ℤ) * ((j : ℕ) - (j' : ℕ) : ℤ) * ((γ : SL(2, ℤ)) : M2) 1 1 :=
        Dvd.intro (((γ' : SL(2, ℤ)) : M2) 1 0 - ((γ : SL(2, ℤ)) : M2) 1 0)
          (by linear_combination -e10 + ((L : ℤ) * ((j' : ℕ) : ℤ)) * e11)
      have hjj : (q : ℤ) ∣ ((j : ℕ) - (j' : ℕ) : ℤ) := by
        by_contra hn
        have hLj : ¬ (q : ℤ) ∣ (L : ℤ) * ((j : ℕ) - (j' : ℕ) : ℤ) := fun hh =>
          (hqZ.dvd_or_dvd hh).elim hqLZ hn
        have a0 := (hqZ.dvd_or_dvd h0).resolve_left hLj
        have a1 := (hqZ.dvd_or_dvd h1).resolve_left hLj
        apply hq1
        rw [← hd]
        exact (Dvd.dvd.mul_left a1 _).sub (Dvd.dvd.mul_right a0 _)
      have hj := j.isLt
      have hj' := j'.isLt
      have hz := Int.eq_zero_of_abs_lt_dvd hjj (abs_sub_lt_iff.mpr ⟨by omega, by omega⟩)
      have hjeq : j = j' := Fin.ext (by omega)
      subst hjeq
      refine Prod.ext (Subtype.ext (Matrix.SpecialLinearGroup.ext _ _ fun i k => ?_)) rfl
      have f00 : ((γ : SL(2, ℤ)) : M2) 0 0 = ((γ' : SL(2, ℤ)) : M2) 0 0 :=
        mul_right_cancel₀ hq0 (by linear_combination e00 - ((L : ℤ) * ((j : ℕ) : ℤ)) * e01)
      have f10 : ((γ : SL(2, ℤ)) : M2) 1 0 = ((γ' : SL(2, ℤ)) : M2) 1 0 :=
        mul_right_cancel₀ hq0 (by linear_combination e10 - ((L : ℤ) * ((j : ℕ) : ℤ)) * e11)
      fin_cases i <;> fin_cases k <;> simp <;> assumption
  · rintro δ ⟨hdet, hL⟩
    rw [Matrix.det_fin_two] at hdet
    by_cases hbd : (q : ℤ) ∣ δ 0 1 ∧ (q : ℤ) ∣ δ 1 1
    · obtain ⟨⟨b', hb⟩, ⟨d', hd⟩⟩ := hbd
      have hdet1 : (!![δ 0 0, b'; δ 1 0, d'] : M2).det = 1 := by
        rw [Matrix.det_fin_two_of]
        apply mul_left_cancel₀ hq0
        rw [hb, hd] at hdet
        linear_combination hdet
      let g : SL(2, ℤ) := ⟨_, hdet1⟩
      have hg : g ∈ Gamma0 L := by
        rw [Gamma0_mem]
        have : ((δ 1 0 : ℤ) : ZMod L) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hL
        simpa [g] using this
      refine ⟨(⟨g, hg⟩, none), trivial, ?_⟩
      ext i k
      fin_cases i <;> fin_cases k <;> simp [g, repL, Matrix.mul_apply, Fin.sum_univ_two, hb, hd] <;> ring
    · have hu : ∃ u : ZMod q, ((δ 0 0 : ℤ) : ZMod q) = (L : ZMod q) * u * ((δ 0 1 : ℤ) : ZMod q) ∧
          ((δ 1 0 : ℤ) : ZMod q) = (L : ZMod q) * u * ((δ 1 1 : ℤ) : ZMod q) := by
        apply exists_kernel_param
        · rw [Ne, ZMod.natCast_eq_zero_iff]; exact hqL
        · have := congrArg (fun x : ℤ => (x : ZMod q)) hdet
          simpa using this
        · by_contra hn
          push_neg at hn
          exact hbd ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hn.1,
            (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hn.2⟩
      obtain ⟨u, hu0, hu1⟩ := hu
      set j : Fin q := ⟨u.val, ZMod.val_lt u⟩ with hjdef
      have hju : (((j : ℕ) : ℤ) : ZMod q) = u := by simp [hjdef]
      obtain ⟨x, hx⟩ : (q : ℤ) ∣ δ 0 0 - L * (j : ℕ) * δ 0 1 := by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        push_cast at hju ⊢
        rw [hju, hu0]; ring
      obtain ⟨z, hz⟩ : (q : ℤ) ∣ δ 1 0 - L * (j : ℕ) * δ 1 1 := by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        push_cast at hju ⊢
        rw [hju, hu1]; ring
      have hcop : IsCoprime (L : ℤ) (q : ℤ) :=
        Nat.isCoprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd hq).mpr hqL).symm
      have hLz : (L : ℤ) ∣ z := by
        apply hcop.dvd_of_dvd_mul_left
        rw [← hz]
        exact dvd_sub hL (Dvd.dvd.mul_right (Dvd.dvd.mul_right (dvd_refl _) _) _)
      have hdet1 : (!![x, δ 0 1; z, δ 1 1] : M2).det = 1 := by
        rw [Matrix.det_fin_two_of]
        apply mul_left_cancel₀ hq0
        linear_combination -(δ 1 1) * hx + δ 0 1 * hz + hdet
      let g : SL(2, ℤ) := ⟨_, hdet1⟩
      have hg : g ∈ Gamma0 L := by
        rw [Gamma0_mem]
        have : ((z : ℤ) : ZMod L) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hLz
        simpa [g] using this
      refine ⟨(⟨g, hg⟩, some j), trivial, ?_⟩
      ext i k
      fin_cases i <;> fin_cases k <;> simp [g, repL, Matrix.mul_apply, Fin.sum_univ_two] <;>
        first | linear_combination -hx | linear_combination -hz

end GlobalTheory.EisM
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsLeftGamma0CosetDecompositionHeckeRepLowerLevelStatement

section

@[expose] public section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.isLeftGamma0CosetDecomposition_heckeRepLowerLevel : ∀ L q : ℕ, q.Prime → ¬ q ∣ L → LRep L (DT L q) (repL L q) := by
  first | exact @GlobalTheory.EisM.repL_LRep | exact GlobalTheory.EisM.repL_LRep | (intros; apply GlobalTheory.EisM.repL_LRep <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumSlashHeckeRepLowerHeckeVEigenform

section

@[expose] public section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

private theorem slz_const_mul (k : ℕ) (δ : M2) (c : ℂ) (g : ℍ → ℂ) (τ : ℍ) :
    slz k δ (fun σ => c * g σ) τ = c * slz k δ g τ := by
  unfold slz; ring

private theorem slz_sub (k : ℕ) (δ : M2) (g g' : ℍ → ℂ) (τ : ℍ) :
    slz k δ (fun σ => g σ - g' σ) τ = slz k δ g τ - slz k δ g' τ := by
  unfold slz; ring

private theorem slz_sum {ι : Type} (s : Finset ι) (k : ℕ) (δ : M2) (g : ι → ℍ → ℂ) (τ : ℍ) :
    slz k δ (fun σ => ∑ i ∈ s, g i σ) τ = ∑ i ∈ s, slz k δ (g i) τ := by
  unfold slz; rw [Finset.mul_sum]

theorem qs_Vo_slz (k l : ℕ) (hl : 0 < l) (a : ℕ → ℂ) (ha : PolyB a) (τ : ℍ) :
    qs (Vo l a) τ = ((l : ℂ) ^ (k - 1))⁻¹ * slz k !![(l : ℤ), 0; 0, 1] (qs a) τ := by
  have hlC : (l : ℂ) ≠ 0 := by exact_mod_cast hl.ne'
  have him : 0 < ((l : ℂ) * (τ : ℂ)).im := by
    simp only [Complex.mul_im, Complex.natCast_re, Complex.natCast_im, zero_mul, add_zero]
    exact mul_pos (by exact_mod_cast hl) τ.im_pos
  have hV := (GlobalTheory.T.coeffHeckeVOperator_polynomialGrowth_qExpansion l a hl ha).2 τ ⟨(l : ℂ) * τ, him⟩ rfl
  rw [hV]
  unfold slz
  simp only [Matrix.det_fin_two_of, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.head_fin_const]
  push_cast
  simp only [zero_mul, zero_add, mul_one, mul_zero, sub_zero, add_zero, div_one, one_pow, inv_one]
  rw [ofComplex_apply_of_im_pos him]
  field_simp

end GlobalTheory.EisM

namespace GlobalTheory.EisM

private theorem qs_smul (t : ℂ) (a : ℕ → ℂ) : qs (t • a) = fun τ => t * qs a τ := by
  funext τ; unfold qs
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
  exact tsum_mul_left

theorem sum_slz_repL_Vo : ∀ (k N l : ℕ) (ε : DirichletCharacter ℂ N) (h : ℕ → ℂ) (t : ℂ), 1 ≤ k → 0 < N → l.Prime → ¬ l ∣ N → MF k N (ch ε) h → To k (ch ε l) l h = t • h → ∀ τ : ℍ, ∑ j : Fin l, slz k (repL (N * l) l (some j)) (qs (Vo l h)) τ = ch ε⁻¹ l * (t * qs (Vo l h) τ - (l : ℂ)⁻¹ * qs h τ) := by
  intro k N l ε h t hk hN hl hlN hMF hT τ
  have hl0 : 0 < l := hl.pos
  have hlC : (l : ℂ) ≠ 0 := by exact_mod_cast hl0.ne'
  set F := qs h with hF
  set D : M2 := !![(l : ℤ), 0; 0, 1] with hD
  set E : M2 := !![(1 : ℤ), 0; 0, (l : ℤ)] with hE
  have hcoc := GlobalTheory.T.slashIntMatrixPosDet_properties k

  have hTq := (GlobalTheory.T.coeffHeckeTOperator_qExpansion_slashSum k l (ch ε) h hk hl0 (by simp [ch]) hMF.1).2
  rw [hT, qs_smul] at hTq
  have hind := GlobalTheory.T.heckeCharacterSlashSum_indep_reps k N N ε (DT N l) (Option (Fin l)) (Option (Fin l)) (repT l) (repL N l) F hk dvd_rfl
    (fun δ hδ => ⟨by rw [hδ.1]; exact_mod_cast hl0, hδ.2⟩) (GlobalTheory.T.isLeftGamma0CosetDecomposition_heckeRepTOperator N l hl hlN) (GlobalTheory.T.isLeftGamma0CosetDecomposition_heckeRepLowerLevel N l hl hlN) hMF.2
  have hcop : Nat.Coprime l N := (Nat.Prime.coprime_iff_not_dvd hl).2 hlN
  have hu : IsUnit (((l : ℤ) : ZMod N)) := by
    rw [Int.cast_natCast]; exact (ZMod.isUnit_iff_coprime l N).2 hcop
  have hεl : ch ε l ≠ 0 := by
    unfold ch; exact (IsUnit.map ε hu).ne_zero
  have hinv : ch ε⁻¹ l = (ch ε l)⁻¹ := by
    unfold ch; rw [MulChar.inv_apply_eq_inv']
  have key : ∀ σ : ℍ, ∑ j : Fin l, slz k (repL N l (some j)) F σ = (ch ε l)⁻¹ * (t * F σ - slz k E F σ) := by
    intro σ
    have h1 := congrFun hTq σ
    rw [hind] at h1
    unfold hsum at h1
    rw [Fintype.sum_option] at h1
    have h2 : repL N l none = E := rfl
    rw [h2] at h1
    have h3 : ∀ j : Fin l, ch ε (repL N l (some j) 0 0) = ch ε l := by
      intro j; simp [repL]
    have h4 : ch ε (E 0 0) = 1 := by simp [hE, ch]
    simp only [h3, h4, one_mul, ← Finset.mul_sum] at h1
    field_simp
    rw [← hF] at h1
    linear_combination -h1
  have hVfun : qs (Vo l h) = fun σ => ((l : ℂ) ^ (k - 1))⁻¹ * slz k D F σ := by
    funext σ; exact qs_Vo_slz k l hl0 h hMF.1 σ
  have hdetD : 0 < D.det := by simp [hD, Matrix.det_fin_two_of]; exact_mod_cast hl0
  have hdetE : 0 < E.det := by simp [hE, Matrix.det_fin_two_of]; exact_mod_cast hl0
  have hdetA : ∀ (L : ℕ) (j : Fin l), 0 < (repL L l (some j)).det := by
    intro L j; simp [repL, Matrix.det_fin_two_of]; exact_mod_cast hl0
  have hmat : ∀ j : Fin l, D * repL (N * l) l (some j) = repL N l (some j) * D := by
    intro j
    ext i m; fin_cases i <;> fin_cases m <;> simp [hD, repL, Matrix.mul_apply, Fin.sum_univ_two] <;> push_cast <;> ring
  have hED : E * D = !![((l : ℕ) : ℤ), 0; 0, ((l : ℕ) : ℤ)] := by
    ext i m; fin_cases i <;> fin_cases m <;> simp [hD, hE, Matrix.mul_apply, Fin.sum_univ_two]
  have hterm : ∀ j : Fin l, slz k (repL (N * l) l (some j)) (qs (Vo l h)) τ =
      ((l : ℂ) ^ (k - 1))⁻¹ * slz k D (slz k (repL N l (some j)) F) τ := by
    intro j
    rw [hVfun, slz_const_mul]
    congr 1
    rw [← (hcoc F hk).1 D _ hdetD (hdetA _ j), hmat j, (hcoc F hk).1 _ D (hdetA _ j) hdetD]
  simp only [hterm]
  rw [← Finset.mul_sum, ← slz_sum]
  have hfun : (fun σ => ∑ j : Fin l, slz k (repL N l (some j)) F σ) = fun σ => (ch ε l)⁻¹ * (t * F σ - slz k E F σ) := by
    funext σ; exact key σ
  rw [hfun, slz_const_mul, slz_sub, slz_const_mul]
  have hDE : slz k D (slz k E F) τ = (l : ℂ) ^ k / (l : ℂ) ^ 2 * F τ := by
    rw [← (hcoc F hk).1 E D hdetE hdetD, hED]
    exact (hcoc F hk).2.2.2.2 l τ hl0
  rw [hDE, hinv]
  have hV := qs_Vo_slz k l hl0 h hMF.1 τ
  rw [hV]
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  field_simp
  ring

end GlobalTheory.EisM
end
end
