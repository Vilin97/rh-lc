module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.JointQ
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LogClassNumberLeLogAbsDiscrDiv
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsImagQuadraticHost
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.FieldSizeMonotone
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.FieldSizeSupAdd
public import Development.AbelianVarietyTheory.Definitions.Foundations.RootOfUnityEightQMemCoeffGaloisSubfield
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.FrameFacts
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.SzAdjoinRootOfUnity
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.SzFieldRangeEmbedding
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DegreeRootDiscrBoundKummerFieldOfPowerIdealRootsStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FieldDatumSizeLogDiscriminantStatement
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RayClassFieldDegreeLeAndRootDiscrBound
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Topology.Sheaves.Init
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat

-- Source module: Development.AbelianVarietyTheory.Proofs.HeightProofs.HostXiOrderBounds

section

@[expose] public section

set_option autoImplicit false

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory.Mem GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.FieldSize
open scoped IntermediateField

namespace GlobalTheory.FieldSize

theorem card_GL_zmod_le (r g : ℕ) (hg : g ≠ 0) : Nat.card (GL (Fin r) (ZMod g)) ≤ g ^ (r ^ 2) := by
  have : NeZero g := ⟨hg⟩
  have h := Nat.card_le_card_of_injective (Units.val : GL (Fin r) (ZMod g) → Matrix (Fin r) (Fin r) (ZMod g))
    Units.val_injective
  refine h.trans (le_of_eq ?_)
  unfold Matrix
  rw [Nat.card_fun, Nat.card_fun, Nat.card_zmod, ← pow_mul]
  simp [sq]

theorem card_units_quot_le (E : Type) [Field E] [NumberField E] (N : ℕ) (hN : N ≠ 0) :
    0 < Nat.card (𝓞 E ⧸ Ideal.span {(N : 𝓞 E)})ˣ ∧
      Nat.card (𝓞 E ⧸ Ideal.span {(N : 𝓞 E)})ˣ ≤ N ^ Module.finrank ℚ E := by
  have hc : Nat.card (𝓞 E ⧸ Ideal.span {(N : 𝓞 E)}) = N ^ Module.finrank ℚ E := by
    rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, Ideal.absNorm_span_natCast, RingOfIntegers.rank]
  have : Finite (𝓞 E ⧸ Ideal.span {(N : 𝓞 E)}) := Nat.finite_of_card_ne_zero (by rw [hc]; positivity)
  exact ⟨Nat.card_pos, hc ▸ Nat.card_le_card_of_injective _ Units.val_injective⟩

theorem roots_sizes (P : Pre) (L : ℝ) (h : HostSz P.host L) :
    Real.log P.restRowsFiniteGroupCard ≤ P.R.f * (P.R.r : ℝ) ^ 2 * (18 * L + 2) ∧
      (∀ p ∈ [P.host.pde, P.host.pde'], 0 < xiOrd P.host (P.host.g 0 * P.host.g 1 * p) ∧
        Real.log (xiOrd P.host (P.host.g 0 * P.host.g 1 * p)) ≤
          1 + Real.log (classNumber P.host.E) + 2 * P.R.f * (21 * L)) ∧ 8 ≤ P.R.f ∧ 2 * P.R.m ≤ P.R.r := by
  have hg : ∀ k, P.host.g k ≠ 0 := fun k => (P.host.g_prime k).ne_zero
  have hg' : ∀ k, (P.host.g k : ℝ) ≠ 0 := fun k => Nat.cast_ne_zero.2 (hg k)
  have h0 := h.g 0
  have h1 := h.g 1
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hle : P.restRowsFiniteGroupCard ≤ (P.host.g 0 * P.host.g 1) ^ (P.R.f * P.R.r ^ 2) := by
      unfold Pre.restRowsFiniteGroupCard
      rw [Fin.prod_univ_two, mul_pow, mul_comm P.R.f, pow_mul, pow_mul]
      exact Nat.mul_le_mul (Nat.pow_le_pow_left (card_GL_zmod_le _ _ (hg 0)) _)
        (Nat.pow_le_pow_left (card_GL_zmod_le _ _ (hg 1)) _)
    have hpos : (0 : ℝ) < P.restRowsFiniteGroupCard := Nat.cast_pos.2 P.restRowsFiniteGroupCard_pos
    refine (Real.log_le_log hpos (Nat.cast_le.2 hle)).trans ?_
    rw [Nat.cast_pow, Real.log_pow, Nat.cast_mul (P.host.g 0), Real.log_mul (hg' 0) (hg' 1)]
    push_cast
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  · intro p hp
    have hp' : p ≠ 0 ∧ Real.log p ≤ L := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact ⟨(P.level_prime _ P.host.pde_level.1).ne_zero, h.p.1⟩
      · exact ⟨(P.level_prime _ P.host.pde_level.2).ne_zero, h.p.2⟩
    have hN : P.host.g 0 * P.host.g 1 * p ≠ 0 := mul_ne_zero (mul_ne_zero (hg 0) (hg 1)) hp'.1
    obtain ⟨hu, hu'⟩ := card_units_quot_le P.host.E _ hN
    have hE : Module.finrank ℚ P.host.E = 2 * P.R.f := by
      rw [P.host.finrank_cmField, Formalism.BasicNotions.Ranks.f, Formalism.BasicNotions.Ranks.n]
      ring
    have hh : 0 < classNumber P.host.E := classNumber_pos _
    refine ⟨by unfold xiOrd; positivity, ?_⟩
    unfold xiOrd
    generalize Nat.card (𝓞 P.host.E ⧸
        Ideal.span {((P.host.g 0 * P.host.g 1 * p : ℕ) : 𝓞 P.host.E)})ˣ = c at hu hu' ⊢
    have hu1 : (0 : ℝ) < c := Nat.cast_pos.2 hu
    have hh1 : (0 : ℝ) < classNumber P.host.E := Nat.cast_pos.2 hh
    have h2 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
    have h3 := Real.log_le_log hu1 (Nat.cast_le.2 hu')
    have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hp'.1
    rw [hE, Nat.cast_pow, Real.log_pow, Nat.cast_mul (P.host.g 0 * P.host.g 1), Nat.cast_mul (P.host.g 0),
      Real.log_mul (mul_ne_zero (hg' 0) (hg' 1)) hp0, Real.log_mul (hg' 0) (hg' 1), Nat.cast_mul,
      Nat.cast_ofNat] at h3
    have h4 : 2 * (P.R.f : ℝ) * (Real.log (P.host.g 0) + Real.log (P.host.g 1) + Real.log p) ≤
        2 * P.R.f * (21 * L) :=
      mul_le_mul_of_nonneg_left (by linarith [h.len, hp'.2]) (by positivity)
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_ofNat, Real.log_mul (by positivity) hu1.ne',
      Real.log_mul two_ne_zero hh1.ne']
    linarith
  · have he := P.host.two_le_e
    have : 2 ^ 2 ≤ 2 ^ P.R.e := Nat.pow_le_pow_right two_pos he
    have h2 := P.R.toFrame.two_pow_le_ord
    unfold Ranks.f Ranks.n
    omega
  · have := P.R.m_add_three_le_k
    unfold Ranks.r
    omega

end GlobalTheory.FieldSize
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RayClassFieldDegreeLeAndRootDiscrBoundStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host GlobalTheory.NT GlobalTheory.Mem GlobalTheory.Mem.Fld GlobalTheory.FieldSize
open scoped IntermediateField

theorem _root_.GlobalTheory.T.rayClassField_degree_le_and_rootDiscrBound : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (φ : E →+* ℂ) (N : ℕ) (M : IntermediateField ℚ ℂ) (h : IsRayFieldIn φ (natIdeal E N) M), N ≠ 0 → degOver φ M h.emb_mem ≤ classNumber E * N ^ Module.finrank ℚ E ∧ Sz M (Real.log (Module.finrank ℚ E) + Real.log (degOver φ M h.emb_mem)) (Real.log |((discr E : ℤ) : ℝ)| / Module.finrank ℚ E + Real.log N + Real.log (degOver φ M h.emb_mem)) := by
  first | exact @GlobalTheory.Mem.Fld.RaySize.degOver_le_and_sz | exact GlobalTheory.Mem.Fld.RaySize.degOver_le_and_sz | (intros; apply GlobalTheory.Mem.Fld.RaySize.degOver_le_and_sz <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaFieldDegreeRootDiscrBoundedByRingPolynomial

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host GlobalTheory.NT GlobalTheory.Mem GlobalTheory.Mem.Fld GlobalTheory.FieldSize
open scoped IntermediateField

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldSize

theorem om_sizes_le_poR (f r L lE lh lN lhs lG lr ld rk ldeg : ℝ) (hf : 8 ≤ f) (hr : 62 ≤ r) (hL : 4 ≤ L)
    (hlf : Real.log f ≤ L) (hE0 : 0 ≤ lE) (hE : lE ≤ 2 * L)
    (hh : lh ≤ f * lE + 2 * f * Real.log (1 + f * lE)) (hN : lN ≤ 20 * L + 2) (hs0 : 0 ≤ lhs)
    (hs : lhs ≤ lh + 2 * f * lN) (hG : lG ≤ f * r ^ 2 * (18 * L + 2)) (hr' : lr ≤ lG + 24)
    (hd : ld ≤ 4 * L) (hk : rk ≤ 2 * f) (hdeg : ldeg ≤ 1 + L) :
    (ld + 20) + (ldeg + lhs) + lr + (ldeg + ((rk + 2) * lhs + lh)) ≤ 19 * f * r ^ 2 * L + 198 * f ^ 2 * L ∧
    (3 * ld + 20) + (lE + lN + lhs) + lr + (lE + ((rk + 2) * lhs + lh)) ≤ 19 * f * r ^ 2 * L + 198 * f ^ 2 * L := by
  have hf0 : 0 < f := by linarith
  have hL0 : 0 < L := by linarith
  have hfE0 : 0 ≤ f * lE := mul_nonneg hf0.le hE0
  have hfE : f * lE ≤ f * (2 * L) := mul_le_mul_of_nonneg_left hE hf0.le
  have hfL : 32 ≤ f * L := by nlinarith
  have h1 : Real.log (1 + f * lE) ≤ Real.log (f * (3 * L)) := Real.log_le_log (by linarith) (by nlinarith)
  have h2 : Real.log (f * (3 * L)) = Real.log f + Real.log (3 * L) := Real.log_mul hf0.ne' (by positivity)
  have h3 : Real.log (3 * L) ≤ 3 * L - 1 := Real.log_le_sub_one_of_pos (by positivity)
  have h4 : Real.log (1 + f * lE) ≤ 4 * L := by linarith
  have h5 : 2 * f * Real.log (1 + f * lE) ≤ 2 * f * (4 * L) := mul_le_mul_of_nonneg_left h4 (by positivity)
  have h6 : lh ≤ 10 * (f * L) := by nlinarith
  have h7 : 2 * f * lN ≤ 2 * f * (20 * L + 2) := mul_le_mul_of_nonneg_left hN (by positivity)
  have h8 : 4 * f ≤ f * L := by nlinarith
  have h9 : lhs ≤ 51 * (f * L) := by nlinarith
  have h10 : (rk + 2) * lhs ≤ (2 * f + 2) * (51 * (f * L)) :=
    mul_le_mul_of_nonneg_right (by linarith) hs0 |>.trans (mul_le_mul_of_nonneg_left h9 (by linarith))
  have h11 : f * r ^ 2 * 2 ≤ f * r ^ 2 * L := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have h12 : 8 * (f * L) ≤ f * (f * L) := mul_le_mul_of_nonneg_right hf (by positivity)
  have h13 : f * (f * L) = f ^ 2 * L := by ring
  constructor <;> nlinarith

theorem sz_Om_poR : RayField → ∀ (P : Pre) (δ : FieldDat P) (L : ℝ), HostSz P.host L → Sz δ.Om (poR P.R L) (poR P.R L) := by
  intro hR P δ L hL
  have hcm : IsCMField P.host.E := P.host.isCMField_hostE
  obtain ⟨K, _, _, hK2, hKd, -, hKE, -, hdeg⟩ := exists_hostK P.R P.host
  have hE := sz_fieldRange_embedding P.host.E P.host.φ₀
  set lE : ℝ := Real.log |((discr P.host.E : ℤ) : ℝ)| / Module.finrank ℚ P.host.E with hlE
  have hlE0 : 0 ≤ lE := by
    refine div_nonneg (Real.log_nonneg ?_) (Nat.cast_nonneg _)
    exact_mod_cast Int.one_le_abs (discr_ne_zero P.host.E)
  have hlE' : lE = Real.log |((discr P.host.E : ℤ) : ℝ)| / (2 * P.R.f) := by rw [hlE, hdeg]; push_cast; rfl
  have hrd : lE ≤ 2 * L := hlE' ▸ hL.rd

  have hd : Real.log (P.host.d : ℝ) ≤ 4 * L := by
    obtain ⟨_, -, h⟩ := sz_mono_and_of_le.2 _ _ _ _ hKE hE
    have h' : Real.log |(discr K : ℝ)| / Module.finrank ℚ K ≤ lE := h
    rw [hK2, hKd] at h'
    push_cast at h'
    rw [abs_neg, abs_of_nonneg (Nat.cast_nonneg _)] at h'
    linarith

  have hM' := GlobalTheory.T.field_datum_size_log_discriminant hR P δ
  obtain ⟨hdeg_le, hray⟩ := GlobalTheory.T.rayClassField_degree_le_and_rootDiscrBound P.host.E P.host.φ₀ (modulus P) δ.ray δ.isRay (modulus_ne_zero P)
  have hcyc : Sz (cycField (rootOrder P)) (Real.log (rootOrder P)) (Real.log (rootOrder P)) :=
    sz_adjoin_rootOfUnity _ (Nat.pos_of_ne_zero (rootOrder_ne_zero P))
  have hV : Sz δ.V _ _ := GlobalTheory.T.degreeRootDiscrBound_kummerFieldOfPowerIdealRoots P.host.E P.host.φ₀ δ.hstar δ.hstar_pos
  have hall := sz_sup _ _ _ _ _ _ (sz_sup _ _ _ _ _ _ (sz_sup _ _ _ _ _ _ hM' hray) hcyc) hV
  change Sz (δ.M' ⊔ δ.ray ⊔ cycField (rootOrder P) ⊔ δ.V) _ _

  obtain ⟨hG, -, hf8, -⟩ := roots_sizes P L hL
  have hf0 : (0 : ℝ) < P.R.f := by have : 8 ≤ P.R.f := hf8; exact_mod_cast (by omega : 0 < P.R.f)
  have hcl := GlobalTheory.log_classNumber_le_log_abs_discr_div P.host.E P.R.f hdeg
  rw [← hlE'] at hcl
  have hh0 : 0 < classNumber P.host.E := classNumber_pos _

  have hg0 := (P.host.g_prime 0).pos
  have hg1 := (P.host.g_prime 1).pos
  have hp := P.host.pde_prime.pos
  have hp' := P.host.pde'_prime.pos
  have hN : Real.log (modulus P : ℝ) ≤ 20 * L + 2 := by
    have e : Real.log (modulus P : ℝ) = Real.log (P.host.g 0) + Real.log (P.host.g 1) + Real.log P.host.pde +
        Real.log P.host.pde' := by
      simp only [modulus]; push_cast
      rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity)]
    have := hL.g 0
    have := hL.g 1
    have := hL.p
    rw [e]; linarith [this.1, this.2]

  have hs0 : 0 ≤ Real.log (δ.hstar : ℝ) := Real.log_natCast_nonneg _
  have hs : Real.log (δ.hstar : ℝ) ≤ Real.log (classNumber P.host.E) + 2 * P.R.f * Real.log (modulus P : ℝ) := by
    have h1 : (δ.hstar : ℝ) ≤ (classNumber P.host.E : ℝ) * (modulus P : ℝ) ^ Module.finrank ℚ P.host.E := by
      exact_mod_cast hdeg_le
    have h2 := Real.log_le_log (by exact_mod_cast δ.hstar_pos) h1
    rw [Real.log_mul (by positivity) (pow_ne_zero _ (by exact_mod_cast modulus_ne_zero P)), Real.log_pow, hdeg] at h2
    push_cast at h2
    linarith

  have hr : Real.log (rootOrder P : ℝ) ≤ Real.log P.restRowsFiniteGroupCard + 24 := by
    have hc := P.restRowsFiniteGroupCard_pos
    have h1 : (rootOrder P : ℝ) ≤ (P.restRowsFiniteGroupCard : ℝ) * ((3 ^ 4 * 5 ^ 4 : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_of_dvd (by positivity) (Nat.lcm_dvd_mul _ _)
    have h2 := Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero (rootOrder_ne_zero P)) h1
    rw [Real.log_mul (by positivity) (by positivity)] at h2
    have e : Real.log ((3 ^ 4 * 5 ^ 4 : ℕ) : ℝ) = 4 * Real.log 3 + 4 * Real.log 5 := by
      rw [show ((3 ^ 4 * 5 ^ 4 : ℕ) : ℝ) = (3 : ℝ) ^ 4 * (5 : ℝ) ^ 4 by norm_num,
        Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]; push_cast; ring
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num)
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 5 by norm_num)
    linarith

  have hk : (NumberField.Units.rank P.host.E : ℝ) ≤ 2 * P.R.f := by
    have : NumberField.Units.rank P.host.E ≤ Module.finrank ℚ P.host.E := by
      rw [NumberField.Units.rank, ← NumberField.InfinitePlace.card_add_two_mul_card_eq_rank,
        NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces]; omega
    rw [hdeg] at this
    exact_mod_cast this
  have d1 : Real.log (Module.finrank ℚ P.host.E) ≤ 1 + L := by
    rw [hdeg]; push_cast
    rw [Real.log_mul (by norm_num) (by positivity)]
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    have := hL.deg
    linarith
  have hnum := om_sizes_le_poR P.R.f P.R.r L lE (Real.log (classNumber P.host.E)) (Real.log (modulus P : ℝ))
    (Real.log (δ.hstar : ℝ)) (Real.log P.restRowsFiniteGroupCard) (Real.log (rootOrder P : ℝ)) (Real.log (P.host.d : ℝ))
    (NumberField.Units.rank P.host.E) (Real.log (Module.finrank ℚ P.host.E)) (by exact_mod_cast hf8)
    (by exact_mod_cast hL.rank) hL.len hL.deg hlE0 hrd hcl hN hs0 hs hG hr hd hk d1
  refine sz_mono_and_of_le.1 _ _ _ _ _ hall ?_ ?_
  · unfold poR; exact hnum.1
  · unfold poR; exact hnum.2

end GlobalTheory.FieldSize

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaFieldDegreeRootDiscrBoundedByRingPolynomialStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host GlobalTheory.NT GlobalTheory.Mem GlobalTheory.Mem.Fld GlobalTheory.FieldSize
open scoped IntermediateField

theorem _root_.GlobalTheory.T.omegaField_degree_rootDiscr_bounded_by_ringPolynomial : RayField → ∀ (P : Pre) (δ : FieldDat P) (L : ℝ), HostSz P.host L → Sz δ.Om (poR P.R L) (poR P.R L) := by
  first | exact @GlobalTheory.FieldSize.sz_Om_poR | exact GlobalTheory.FieldSize.sz_Om_poR | (intros; apply GlobalTheory.FieldSize.sz_Om_poR <;> assumption)
end
end
