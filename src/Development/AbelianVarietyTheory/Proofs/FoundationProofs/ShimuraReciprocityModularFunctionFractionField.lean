module

public import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExpTwoPiIRatInFieldRootsOfUnityPropertiesStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisExponentRootOfUnityExpTwoPiIStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFunctionFractionFieldSlRightActionStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmpPropsStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CuspExpansionCoeffConjOfQExpansionConjStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsComplexRingEquivExtendingSubfieldAutStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FractionFieldExtClosureInjectiveStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LevelNFunctionGaloisConjQExpansionStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlTwoDiagConjCongruenceIffDiagOneUnitMatrixEqStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GammaLeOfDvdStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemModularFunctionRingOverIffHasSomeLevelOverStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiagOneUnitConjLiftsSl2IntReductionModStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisSlTwoActionModularFunctionRingOfCongr

section

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem gal_sl_io_of_cong :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε) (a : GlobalTheory.FN.ring ε.range) (N w : ℕ), 0 < N → Lv ε.range N w a → ∀ (s : Ω ≃ₐ[ℚ] Ω) (d : ℤ), s (eOm ε (1 / N)) = eOm ε (1 / N) ^ d → ∀ γ γ' : SL(2, ℤ), Cong N d γ γ' → T.gal s (T.sl (ofSL γ) (T.io a)) = T.sl (ofSL γ') (T.gal s (T.io a)) := by
  intro Ω _ _ _ ε T a N w hN hLv s d hs γ γ' hC
  haveI : NeZero N := ⟨hN.ne'⟩
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_complex_ringEquiv_extending_subfield_aut Ω ε s.toRingEquiv
  have hg' : ∀ x, g (ε x) = ε (s x) := hg
  obtain ⟨u, hu, hZ⟩ := (GlobalTheory.T.galois_exponent_rootOfUnity_expTwoPiI Ω ε s N hN).2 d hs
  have hE : ∀ x ∈ ε.range, g x ∈ ε.range := by
    rintro _ ⟨y, rfl⟩
    exact ⟨s y, (hg' y).symm⟩
  obtain ⟨f', hf'L, hf'C⟩ := GlobalTheory.T.levelN_function_galois_conj_qExpansion g ε.range N u w (a : ℍ → ℂ) hE (hZ g hg') hLv
  let a' : GlobalTheory.FN.ring ε.range := ⟨f', mem_ring_of_inR ⟨N, w, hN, hf'L⟩⟩
  obtain ⟨hext, hcmp, hexpinj, -⟩ := GlobalTheory.T.fractionField_ext_closure_injective Ω ε T
  obtain ⟨-, -, hSL, -⟩ := GlobalTheory.T.cmp_mul_ofSL_and_up_cmp_eq_up_mob

  have key : ∀ γ γ' : SL(2, ℤ), dg u * redGL N γ' = redGL N γ * dg u →
      T.gal s (T.sl (ofSL γ) (T.io a)) = T.sl (ofSL γ') (T.io a') := by
    intro γ γ' hM
    obtain ⟨b, hb, hbio⟩ := hcmp (ofSL γ) a
    obtain ⟨b', hb', hb'io⟩ := hcmp (ofSL γ') a'
    rw [hbio, hb'io]
    apply hexpinj
    ext r
    rw [T.gal_exp]
    have hb1 : (b : ℍ → ℂ) = fun τ => (a : ℍ → ℂ) (γ • τ) := by rw [hb, hSL]
    have hb2 : (b' : ℍ → ℂ) = fun τ => f' (γ' • τ) := by rw [hb', hSL]
    refine Eq.symm ?_
    refine GlobalTheory.T.cuspExpansion_coeff_conj_of_qExpansion_conj Ω ε s.toRingEquiv.toRingHom g N w b b' _ _ hg' hN ?_ ?_ (T.exp_io b) (T.exp_io b') r
    · rw [hb1]; exact hLv.2 γ
    · rw [hb1, hb2]; exact hf'C γ γ' hM
  have h1 : T.gal s (T.io a) = T.io a' := by
    have hM1 : dg u * redGL N 1 = redGL N 1 * dg u := by simp [redGL]
    have := key 1 1 hM1
    obtain ⟨c, hc, hcio⟩ := hcmp (ofSL 1) a
    obtain ⟨c', hc', hc'io⟩ := hcmp (ofSL 1) a'
    have e1 : c = a := Subtype.ext (by rw [hc, hSL]; funext τ; simp)
    have e2 : c' = a' := Subtype.ext (by rw [hc', hSL]; funext τ; simp [a'])
    rw [hcio, hc'io, e1, e2] at this
    exact this
  rw [h1]
  exact key γ γ' ((GlobalTheory.T.slTwoDiagConjCongruence_iff_diagOneUnit_matrix_eq N d u hu γ γ').mp hC)

end GlobalTheory.FN
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisSlTwoActionModularFunctionRingOfCongrStatement

section

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.galois_slTwo_action_modularFunctionRing_of_congr : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε) (a : GlobalTheory.FN.ring ε.range) (N w : ℕ), 0 < N → Lv ε.range N w a → ∀ (s : Ω ≃ₐ[ℚ] Ω) (d : ℤ), s (eOm ε (1 / N)) = eOm ε (1 / N) ^ d → ∀ γ γ' : SL(2, ℤ), Cong N d γ γ' → T.gal s (T.sl (ofSL γ) (T.io a)) = T.sl (ofSL γ') (T.gal s (T.io a)) := by
  first | exact @GlobalTheory.FN.gal_sl_io_of_cong | exact GlobalTheory.FN.gal_sl_io_of_cong | (intros; apply GlobalTheory.FN.gal_sl_io_of_cong <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ReciprocityLargeLevel

section

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem reciprocity_large_level : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε) (f : T.K), ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N : ℕ, 0 < N → N₀ ∣ N → ∀ (s : Ω ≃ₐ[ℚ] Ω) (d : ℤ), s (eOm ε (1 / N)) = eOm ε (1 / N) ^ d → ∀ γ γ' : SL(2, ℤ), Cong N d γ γ' → T.gal s (T.sl (ofSL γ) f) = T.sl (ofSL γ') (T.gal s f) := by
  intro Ω _ _ _ ε T f
  obtain ⟨a, b, hb, hab⟩ := T.io_surj f
  have hbK : T.io b ≠ 0 := by
    intro h
    exact hb (T.io_inj (by rw [h, map_zero]))
  have hf : f = T.io a / T.io b := by
    rw [eq_div_iff hbK, hab]
  obtain ⟨Na, wa, hNa, hLa⟩ := ((GlobalTheory.T.mem_modularFunctionRingOver_iff_hasSomeLevelOver ε.range).1 a).1 a.2
  obtain ⟨Nb, wb, hNb, hLb⟩ := ((GlobalTheory.T.mem_modularFunctionRingOver_iff_hasSomeLevelOver ε.range).1 b).1 b.2
  refine ⟨Na * Nb, Nat.mul_pos hNa hNb, ?_⟩
  intro N hN hdiv s d hs γ γ' hc
  have hLa' : Lv ε.range N wa a :=
    GlobalTheory.T.lv_mono_of_dvd_of_le ε.range Na N wa wa a hN (dvd_trans (dvd_mul_right Na Nb) hdiv) le_rfl hLa
  have hLb' : Lv ε.range N wb b :=
    GlobalTheory.T.lv_mono_of_dvd_of_le ε.range Nb N wb wb b hN (dvd_trans (dvd_mul_left Nb Na) hdiv) le_rfl hLb
  have ra := GlobalTheory.T.galois_slTwo_action_modularFunctionRing_of_congr Ω ε T a N wa hN hLa' s d hs γ γ' hc
  have rb := GlobalTheory.T.galois_slTwo_action_modularFunctionRing_of_congr Ω ε T b N wb hN hLb' s d hs γ γ' hc
  rw [hf, map_div₀, map_div₀, map_div₀, map_div₀, ra, rb]

end GlobalTheory.FN
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ReciprocityLargeLevelStatement

section

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.exists_level_gal_sl_commute : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε) (f : T.K), ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N : ℕ, 0 < N → N₀ ∣ N → ∀ (s : Ω ≃ₐ[ℚ] Ω) (d : ℤ), s (eOm ε (1 / N)) = eOm ε (1 / N) ^ d → ∀ γ γ' : SL(2, ℤ), Cong N d γ γ' → T.gal s (T.sl (ofSL γ) f) = T.sl (ofSL γ') (T.gal s f) := by
  first | exact @GlobalTheory.FN.reciprocity_large_level | exact GlobalTheory.FN.reciprocity_large_level | (intros; apply GlobalTheory.FN.reciprocity_large_level <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlTwoDiagConjCongruenceLiftLevel

section

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FNCongLift

theorem cong_of_dvd {M N : ℕ} (hMN : M ∣ N) {d : ℤ} {γ γ' : SL(2, ℤ)} (h : Cong N d γ γ') : Cong M d γ γ' := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have key : ∀ x y : ZMod N, x = y → ZMod.castHom hMN (ZMod M) x = ZMod.castHom hMN (ZMod M) y :=
    fun x y hxy => by rw [hxy]
  have k1 := key _ _ h1
  have k2 := key _ _ h2
  have k3 := key _ _ h3
  have k4 := key _ _ h4
  simp only [map_mul, map_intCast] at k1 k2 k3 k4
  exact ⟨k1, k2, k3, k4⟩

theorem cong_congr_d {M : ℕ} {d d' : ℤ} (h : (d : ZMod M) = d') {γ γ' : SL(2, ℤ)} (hc : Cong M d γ γ') :
    Cong M d' γ γ' := by
  unfold Cong at hc ⊢
  rw [← h]
  exact hc

theorem en_eq_of_cong {M : ℕ} {d : ℤ} (hd : IsUnit (d : ZMod M)) {γ γ' γ'' : SL(2, ℤ)}
    (h' : Cong M d γ γ') (h'' : Cong M d γ γ'') :
    ∀ i j, (en γ' i j : ZMod M) = en γ'' i j := by
  obtain ⟨a1, a2, a3, a4⟩ := h'
  obtain ⟨b1, b2, b3, b4⟩ := h''
  intro i j
  fin_cases i <;> fin_cases j
  · simp only [Fin.zero_eta, Fin.isValue]; rw [a1, b1]
  · simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one]; rw [a2, b2]
  · simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one]
    exact hd.mul_left_cancel (a3.trans b3.symm)
  · simp only [Fin.isValue, Fin.mk_one]; rw [a4, b4]

theorem mem_Gamma_iff_en {M : ℕ} (γ : SL(2, ℤ)) :
    γ ∈ CongruenceSubgroup.Gamma M ↔
      (en γ 0 0 : ZMod M) = 1 ∧ (en γ 0 1 : ZMod M) = 0 ∧ (en γ 1 0 : ZMod M) = 0 ∧ (en γ 1 1 : ZMod M) = 1 := by
  rw [CongruenceSubgroup.Gamma_mem]
  simp [en]

theorem mul_inv_mem_Gamma {M : ℕ} {γ' γ'' : SL(2, ℤ)} (h : ∀ i j, (en γ' i j : ZMod M) = en γ'' i j) :
    γ' * γ''⁻¹ ∈ CongruenceSubgroup.Gamma M := by
  rw [CongruenceSubgroup.Gamma_mem']
  have : Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) γ' = Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) γ'' := by
    ext i j
    simpa [en] using h i j
  rw [map_mul, map_inv, this, mul_inv_cancel]

theorem cong_lift : ∀ (M N : ℕ) (d d' : ℤ), 0 < N → M ∣ N → (d : ZMod M) = d' → IsUnit (d' : ZMod N) → (∀ γ γ' : SL(2, ℤ), Cong M d γ γ' → ∃ γ'' : SL(2, ℤ), Cong N d' γ γ'' ∧ γ' * γ''⁻¹ ∈ CongruenceSubgroup.Gamma M) ∧ ∀ δ' ∈ CongruenceSubgroup.Gamma M, ∃ δ ∈ CongruenceSubgroup.Gamma M, Cong N d' δ δ' := by
  intro M N d d' hN hMN hdd' hu
  haveI : NeZero N := ⟨hN.ne'⟩
  have hdM : IsUnit (d : ZMod M) := by
    have := (hu.map (ZMod.castHom hMN (ZMod M)))
    rw [hdd']; simpa using this
  have hdM' : (d' : ZMod M) = d := hdd'.symm
  obtain ⟨u, hu'⟩ := hu
  obtain ⟨ex1, ex2⟩ := GlobalTheory.T.diagOneUnit_conj_lifts_sl2IntReductionMod N u
  refine ⟨fun γ γ' hγ => ?_, fun δ' hδ' => ?_⟩
  · obtain ⟨γ'', hγ''⟩ := ex1 γ
    have hc : Cong N d' γ γ'' := (GlobalTheory.T.slTwoDiagConjCongruence_iff_diagOneUnit_matrix_eq N d' u hu' γ γ'').2 hγ''
    refine ⟨γ'', hc, mul_inv_mem_Gamma (en_eq_of_cong hdM hγ ?_)⟩
    exact cong_congr_d hdM' (cong_of_dvd hMN hc)
  · obtain ⟨δ, hδ⟩ := ex2 δ'
    have hc : Cong N d' δ δ' := (GlobalTheory.T.slTwoDiagConjCongruence_iff_diagOneUnit_matrix_eq N d' u hu' δ δ').2 hδ
    refine ⟨δ, ?_, hc⟩
    have hcM := cong_congr_d hdM' (cong_of_dvd hMN hc)
    obtain ⟨c1, c2, c3, c4⟩ := hcM
    obtain ⟨g1, g2, g3, g4⟩ := (mem_Gamma_iff_en δ').1 hδ'
    rw [mem_Gamma_iff_en]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [← c1, g1]
    · have : (d : ZMod M) * en δ 0 1 = d * 0 := by rw [← c2, g2, mul_zero]
      exact hdM.mul_left_cancel this
    · rw [← c3, g3, mul_zero]
    · rw [← c4, g4]

end GlobalTheory.FNCongLift
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlTwoDiagConjCongruenceLiftLevelStatement

section

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.slTwoDiagConjCongruence_lift_level : ∀ (M N : ℕ) (d d' : ℤ), 0 < N → M ∣ N → (d : ZMod M) = d' → IsUnit (d' : ZMod N) → (∀ γ γ' : SL(2, ℤ), Cong M d γ γ' → ∃ γ'' : SL(2, ℤ), Cong N d' γ γ'' ∧ γ' * γ''⁻¹ ∈ CongruenceSubgroup.Gamma M) ∧ ∀ δ' ∈ CongruenceSubgroup.Gamma M, ∃ δ ∈ CongruenceSubgroup.Gamma M, Cong N d' δ δ' := by
  first | exact @GlobalTheory.FNCongLift.cong_lift | exact GlobalTheory.FNCongLift.cong_lift | (intros; apply GlobalTheory.FNCongLift.cong_lift <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ShimuraReciprocityModularFunctionFractionField

section

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FNRecip

theorem main : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε) (M : ℕ) (f : T.K), 0 < M → (∀ γ ∈ CongruenceSubgroup.Gamma M, T.sl (ofSL γ) f = f) → ∀ ζ : Ω, IsPrimitiveRoot ζ M → ∀ (s : Ω ≃ₐ[ℚ] Ω) (d : ℤ), s ζ = ζ ^ d → ∀ γ γ' : SL(2, ℤ), Cong M d γ γ' → T.gal s (T.sl (ofSL γ) f) = T.sl (ofSL γ') (T.gal s f) := by
  intro Ω _ _ _ ε T M f hM hf ζ hζ s d hsd γ γ' hc
  obtain ⟨N₀, hN₀, hrec⟩ := GlobalTheory.T.exists_level_gal_sl_commute Ω ε T f
  set N := N₀ * M with hNdef
  have hN : 0 < N := Nat.mul_pos hN₀ hM
  obtain ⟨⟨d', hd'⟩, hu⟩ := GlobalTheory.T.galois_exponent_rootOfUnity_expTwoPiI Ω ε s N hN
  obtain ⟨u, hu1, -⟩ := hu d' hd'
  have hunit : IsUnit ((d' : ℤ) : ZMod N) := hu1 ▸ u.isUnit
  set ω := eOm ε (1 / (N : ℚ)) with hω
  have hωp : IsPrimitiveRoot ω N := (GlobalTheory.T.expTwoPiIRatInField_roots_of_unity_properties Ω ε).2.2.2.2.1 N hN
  have hωM : IsPrimitiveRoot (ω ^ N₀) M := hωp.pow hN rfl
  haveI : NeZero M := ⟨hM.ne'⟩
  obtain ⟨i, -, hi⟩ := hωM.eq_pow_of_pow_eq_one hζ.pow_eq_one
  have hsζ : s ζ = ζ ^ d' := by
    rw [← hi, map_pow, map_pow, hd', ← zpow_natCast, ← zpow_natCast, ← zpow_natCast, ← zpow_natCast,
      ← zpow_mul, ← zpow_mul, ← zpow_mul, ← zpow_mul]
    ring_nf
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hM.ne'
  have hdd : (d : ZMod M) = d' := by
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
    have := (hζ.zpow_eq_one_iff_dvd (d' - d)).1 (by
      rw [zpow_sub₀ hζ0, ← hsd, ← hsζ, div_self]; exact (map_ne_zero s).2 hζ0)
    exact this
  obtain ⟨hl1, hl2⟩ := GlobalTheory.T.slTwoDiagConjCongruence_lift_level M N d d' hN (Dvd.intro_left N₀ rfl) hdd hunit
  obtain ⟨γ'', hc'', hκ⟩ := hl1 γ γ' hc
  have hact := GlobalTheory.T.modularFunctionFractionField_sl_rightAction Ω ε T
  have hinv : ∀ δ' ∈ CongruenceSubgroup.Gamma M, T.sl (ofSL δ') (T.gal s f) = T.gal s f := by
    intro δ' hδ'
    obtain ⟨δ, hδ, hcδ⟩ := hl2 δ' hδ'
    have := hrec N hN (Dvd.intro M rfl) s d' hd' δ δ' hcδ
    rw [hf δ hδ] at this
    exact this.symm
  rw [hrec N hN (Dvd.intro M rfl) s d' hd' γ γ'' hc'']
  have hγ' : γ' = (γ' * γ''⁻¹) * γ'' := by group
  rw [hγ', map_mul, hact.2, hinv _ hκ]

end GlobalTheory.FNRecip
end
end
