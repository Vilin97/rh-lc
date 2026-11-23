module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FourierMatch
public import Mathlib.FieldTheory.Separable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsotropicIdempotentCentralizerHermitianStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MatrixCommuteOfCommuteSeparableCharpoly
import Mathlib.Tactic.Linter.Style
public import Mathlib.Topology.Algebra.Group.Units

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCompactPreimageMulStarAnisotropicSubmodule

section

@[expose] public section

open GlobalTheory.JR Matrix

namespace GlobalTheory

theorem mul_star_anisotropic_proper : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (V : Submodule E (Matrix (Fin r) (Fin r) E)), (∀ z ∈ V, z * star z = 0 → z = 0) → ∀ B : Set (Matrix (Fin r) (Fin r) E), IsCompact B → IsCompact {z : Matrix (Fin r) (Fin r) E | z ∈ V ∧ z * star z ∈ B} := by
  intro F E _ _ _ _ hU r V hV B hB
  letI : NormedAddCommGroup (Matrix (Fin r) (Fin r) E) := Matrix.normedAddCommGroup
  letI : NormedSpace E (Matrix (Fin r) (Fin r) E) := Matrix.normedSpace
  haveI : LocallyCompactSpace E := hU.lcE
  haveI : ProperSpace E := ProperSpace.of_locallyCompactSpace E
  haveI : ProperSpace (Matrix (Fin r) (Fin r) E) := FiniteDimensional.proper E _
  have hsE : Continuous (star : E → E) :=
    AddMonoidHomClass.continuous_of_bound (starAddEquiv : E ≃+ E) 1 (fun x => by simp [hU.norm_star])
  haveI : ContinuousStar E := ⟨hsE⟩
  have hQc : Continuous fun z : Matrix (Fin r) (Fin r) E => z * star z :=
    continuous_id.mul continuous_star
  have hQs : ∀ (d : E) (z : Matrix (Fin r) (Fin r) E), (d • z) * star (d • z) = (d * star d) • (z * star z) := by
    intro d z
    rw [star_smul, smul_mul_smul_comm]
  have hnd : ∀ d : E, ‖d * star d‖ = ‖d‖ ^ 2 := by
    intro d; rw [norm_mul, hU.norm_star, sq]
  have hVc : IsClosed (V : Set (Matrix (Fin r) (Fin r) E)) := Submodule.closed_of_finiteDimensional V
  obtain ⟨k, hk⟩ := NormedField.exists_one_lt_norm E
  set A : Set (Matrix (Fin r) (Fin r) E) := {w | w ∈ V ∧ ‖k‖⁻¹ ≤ ‖w‖ ∧ ‖w‖ ≤ 1} with hA
  have hAc : IsCompact A := by
    apply Metric.isCompact_of_isClosed_isBounded
    · exact hVc.inter ((isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const))
    · exact (Metric.isBounded_closedBall (x := (0 : Matrix (Fin r) (Fin r) E)) (r := 1)).subset
        (fun w hw => by simpa using hw.2.2)
  have hkpos : 0 < ‖k‖⁻¹ := inv_pos.mpr (lt_trans one_pos hk)
  have hA0 : ∀ w ∈ A, 0 < ‖w * star w‖ := by
    intro w hw
    apply norm_pos_iff.mpr
    intro h0
    have := hV w hw.1 h0
    have h1 := hw.2.1
    rw [this, norm_zero] at h1
    linarith
  obtain ⟨c, hc0, hc⟩ : ∃ c : ℝ, 0 < c ∧ ∀ w ∈ A, c ≤ ‖w * star w‖ := by
    rcases A.eq_empty_or_nonempty with he | hne
    · exact ⟨1, one_pos, by simp [he]⟩
    · obtain ⟨w₀, hw₀, hmin⟩ := hAc.exists_isMinOn hne (hQc.norm.continuousOn)
      exact ⟨_, hA0 w₀ hw₀, fun w hw => hmin hw⟩
  obtain ⟨R, hR⟩ := (hB.isBounded).subset_closedBall 0
  apply Metric.isCompact_of_isClosed_isBounded
  · exact hVc.inter (hB.isClosed.preimage hQc)
  · apply (Metric.isBounded_closedBall (x := (0 : Matrix (Fin r) (Fin r) E)) (r := Real.sqrt (|R| / c))).subset
    intro z hz
    rw [Metric.mem_closedBall, dist_zero_right]
    have hQR : ‖z * star z‖ ≤ |R| := by
      have := hR hz.2
      rw [Metric.mem_closedBall, dist_zero_right] at this
      exact this.trans (le_abs_self R)
    by_cases hz0 : z = 0
    · rw [hz0, norm_zero]; exact Real.sqrt_nonneg _
    obtain ⟨d, hd0, hd1, hd2, -⟩ := rescale_to_shell hk one_pos hz0
    have hdA : d • z ∈ A := ⟨V.smul_mem d hz.1, by simpa using hd2, hd1.le⟩
    have h1 := hc _ hdA
    rw [hQs, norm_smul, hnd] at h1
    rw [norm_smul] at hd1
    apply Real.le_sqrt_of_sq_le
    rw [le_div_iff₀ hc0]
    have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
    have hdpos : 0 < ‖d‖ := norm_pos_iff.mpr hd0

    have hdz : (‖d‖ * ‖z‖) ^ 2 ≤ 1 := by
      have : 0 ≤ ‖d‖ * ‖z‖ := by positivity
      nlinarith
    have hQ0 : 0 ≤ ‖z * star z‖ := norm_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left h1 (sq_nonneg ‖z‖)]

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCompactPreimageMulStarAnisotropicSubmoduleStatement

section

@[expose] public section

open GlobalTheory.JR Matrix

theorem _root_.GlobalTheory.T.isCompact_preimage_mul_star_anisotropic_submodule : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (V : Submodule E (Matrix (Fin r) (Fin r) E)), (∀ z ∈ V, z * star z = 0 → z = 0) → ∀ B : Set (Matrix (Fin r) (Fin r) E), IsCompact B → IsCompact {z : Matrix (Fin r) (Fin r) E | z ∈ V ∧ z * star z ∈ B} := by
  first | exact @GlobalTheory.mul_star_anisotropic_proper | exact GlobalTheory.mul_star_anisotropic_proper | (intros; apply GlobalTheory.mul_star_anisotropic_proper <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MatrixCommuteOfCommuteSeparableCharpolyStatement

section

@[expose] public section

open Matrix

theorem _root_.GlobalTheory.T.matrix_commute_of_commute_separable_charpoly : ∀ (E : Type) [Field E] (r : ℕ) (A₀ : Matrix (Fin r) (Fin r) E), A₀.charpoly.Separable → ∀ m n : Matrix (Fin r) (Fin r) E, m * A₀ = A₀ * m → n * A₀ = A₀ * n → m * n = n * m := by
  first | exact @GlobalTheory.CommSep.commute_of_commute_separable | exact GlobalTheory.CommSep.commute_of_commute_separable | (intros; apply GlobalTheory.CommSep.commute_of_commute_separable <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCompactPreimageNormCentralizerHermitian

section

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.NormSec

theorem normsec : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (A₀ : Matrix (Fin r) (Fin r) E), A₀.IsHermitian → A₀.charpoly.Separable → ∀ M : Set (GL (Fin r) E), IsCompact M → ∃ S : Set (GL (Fin r) E), IsCompact S ∧ ∀ t : GL (Fin r) E, (t : Matrix (Fin r) (Fin r) E) * A₀ = A₀ * (t : Matrix (Fin r) (Fin r) E) → (∃ m ∈ M, (t : Matrix (Fin r) (Fin r) E) * star (t : Matrix (Fin r) (Fin r) E) = (m : Matrix (Fin r) (Fin r) E)) → ∃ s ∈ S, (s : Matrix (Fin r) (Fin r) E) * A₀ = A₀ * (s : Matrix (Fin r) (Fin r) E) ∧ (s : Matrix (Fin r) (Fin r) E) * star (s : Matrix (Fin r) (Fin r) E) = (t : Matrix (Fin r) (Fin r) E) * star (t : Matrix (Fin r) (Fin r) E) := by
  intro F E _ _ _ _ hU r A₀ hA hsep M hM
  classical
  have hA' : star A₀ = A₀ := by rw [Matrix.star_eq_conjTranspose]; exact hA
  obtain ⟨f, hfA, hff, hffs, haniso⟩ := GlobalTheory.T.exists_isotropic_idempotent_centralizer_hermitian E r A₀ hA hsep
  have hcomm := GlobalTheory.T.matrix_commute_of_commute_separable_charpoly E r A₀ hsep
  have hstarC : ∀ m : Matrix (Fin r) (Fin r) E, m * A₀ = A₀ * m → star m * A₀ = A₀ * star m := by
    intro m hm
    have := congrArg star hm
    rw [star_mul, star_mul, hA'] at this
    exact this.symm
  set g := star f with hg
  set e : Matrix (Fin r) (Fin r) E := 1 - f - g with he
  have hes : star e = 1 - g - f := by rw [he, star_sub, star_sub, star_one, hg, star_star]
  let R := Subring.centralizer ({A₀} : Set (Matrix (Fin r) (Fin r) E))
  have memR : ∀ m : Matrix (Fin r) (Fin r) E, m * A₀ = A₀ * m → m ∈ R := by
    intro m hm
    rw [Subring.mem_centralizer_iff]
    intro x hx
    rw [Set.mem_singleton_iff.1 hx]
    exact hm.symm
  have memR' : ∀ m ∈ R, m * A₀ = A₀ * m := by
    intro m hm
    exact ((Subring.mem_centralizer_iff.1 hm) A₀ rfl).symm
  letI : CommRing R := { (inferInstance : Ring R) with
    mul_comm := fun a b => Subtype.ext (hcomm a.1 b.1 (memR' _ a.2) (memR' _ b.2)) }
  let V : Submodule E (Matrix (Fin r) (Fin r) E) :=
    { carrier := {z | z * A₀ = A₀ * z ∧ z * e = z}
      add_mem' := by
        rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
        exact ⟨by rw [add_mul, mul_add, ha1, hb1], by rw [add_mul, ha2, hb2]⟩
      zero_mem' := ⟨by simp, by simp⟩
      smul_mem' := by
        rintro c a ⟨ha1, ha2⟩
        exact ⟨by rw [Matrix.smul_mul, Matrix.mul_smul, ha1], by rw [Matrix.smul_mul, ha2]⟩ }
  have hV : ∀ z ∈ V, z * star z = 0 → z = 0 := by
    rintro z ⟨hz1, hz2⟩ h0
    have h := haniso z hz1
    rw [hz2] at h
    exact h h0
  let M₁ := (fun u : GL (Fin r) E => (u : Matrix (Fin r) (Fin r) E)) '' M
  let M₂ := (fun u : GL (Fin r) E => ((u⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E)) '' M
  have hM₁ : IsCompact M₁ := hM.image Units.continuous_val
  have hM₂ : IsCompact M₂ := hM.image Units.continuous_coe_inv
  let B₁ := (fun x => x * e) '' M₁
  let B₂ := (fun x => x * e) '' M₂
  have hB₁ : IsCompact B₁ := hM₁.image (continuous_mul_const e)
  have hB₂ : IsCompact B₂ := hM₂.image (continuous_mul_const e)
  have hT₁ := GlobalTheory.T.isCompact_preimage_mul_star_anisotropic_submodule F E r V hV B₁ hB₁
  have hT₂ := GlobalTheory.T.isCompact_preimage_mul_star_anisotropic_submodule F E r V hV B₂ hB₂
  let P₁ := (fun p : Matrix (Fin r) (Fin r) E × Matrix (Fin r) (Fin r) E => p.1 + p.2 * f + g) ''
    ({z | z ∈ V ∧ z * star z ∈ B₁} ×ˢ M₁)
  let P₂ := (fun p : Matrix (Fin r) (Fin r) E × Matrix (Fin r) (Fin r) E => p.1 + p.2 * f + g) ''
    ({z | z ∈ V ∧ z * star z ∈ B₂} ×ˢ M₂)
  have hP₁ : IsCompact P₁ := (hT₁.prod hM₁).image (by fun_prop)
  have hP₂ : IsCompact P₂ := (hT₂.prod hM₂).image (by fun_prop)
  refine ⟨{s | (s : Matrix (Fin r) (Fin r) E) ∈ P₁ ∧ ((s⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) ∈ P₂}, ?_, ?_⟩
  · have := Units.isClosedEmbedding_embedProduct.isCompact_preimage
      (hP₁.prod (hP₂.image MulOpposite.continuous_op))
    convert this using 1
    ext s
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Units.embedProduct_apply, Set.mem_prod]
    rw [MulOpposite.op_injective.mem_set_image]
  rintro t ht ⟨m, hmM, hm⟩
  set T : Matrix (Fin r) (Fin r) E := (t : Matrix (Fin r) (Fin r) E) with hT
  set Ti : Matrix (Fin r) (Fin r) E := ((t⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) with hTi
  set mm : Matrix (Fin r) (Fin r) E := (m : Matrix (Fin r) (Fin r) E) with hmm
  set mi : Matrix (Fin r) (Fin r) E := ((m⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) with hmi
  have cTi : Ti * A₀ = A₀ * Ti := Commute.units_inv_left (u := t) ht
  have cm : mm * A₀ = A₀ * mm := by
    rw [← hm, mul_assoc, hstarC _ ht, ← mul_assoc, ht, mul_assoc]
  have cmi : mi * A₀ = A₀ * mi := Commute.units_inv_left (u := m) cm
  let xT : R := ⟨T, memR _ ht⟩
  let xTp : R := ⟨star T, memR _ (hstarC _ ht)⟩
  let xTi : R := ⟨Ti, memR _ cTi⟩
  let xTip : R := ⟨star Ti, memR _ (hstarC _ cTi)⟩
  let xmi : R := ⟨mi, memR _ cmi⟩
  let xf : R := ⟨f, memR _ hfA⟩
  let xg : R := ⟨g, memR _ (hstarC _ hfA)⟩
  have hfR : xf * xf = xf := Subtype.ext hff
  have hgR : xg * xg = xg := Subtype.ext (by show star f * star f = star f; rw [← star_mul, hff])
  have hfgR : xf * xg = 0 := Subtype.ext hffs
  have hTiR : xT * xTi = 1 := Subtype.ext (Units.mul_inv t)
  have hTpiR : xTp * xTip = 1 := Subtype.ext (by
    show star T * star Ti = 1
    rw [← star_mul, hT, hTi, Units.inv_mul, star_one])
  have hmiR : xmi * (xT * xTp) = 1 := Subtype.ext (by
    show mi * (T * star T) = 1
    rw [hm, hmi, hmm, Units.inv_mul])
  have heR : (1 - xf - xg) * (1 - xf - xg) = 1 - xf - xg := by linear_combination hfR + hgR + 2 * hfgR
  have hefR : (1 - xf - xg) * xf = 0 := by linear_combination -hfR - hfgR
  have hegR : (1 - xf - xg) * xg = 0 := by linear_combination -hgR - hfgR
  let X₀ : R := xT * (1 - xf - xg) + xT * xTp * xf + xg
  let X₁ : R := xTi * (1 - xf - xg) + xmi * xf + xg
  have h01 : X₀ * X₁ = 1 := by
    linear_combination (1 - xf - xg) * (1 - xf - xg) * hTiR + heR + xT * xmi * hefR + xT * hegR +
      xT * xTp * xTi * hefR + xf * xf * hmiR + hfR + xT * xTp * hfgR + xTi * hegR + xmi * hfgR + hgR
  have h10 : X₁ * X₀ = 1 := by rw [mul_comm]; exact h01
  let s : GL (Fin r) E := ⟨X₀.1, X₁.1, congrArg Subtype.val h01, congrArg Subtype.val h10⟩
  have hX₀ : X₀.1 = T * e + mm * f + g := by
    show T * (1 - f - g) + T * star T * f + g = _
    rw [hm]
  have hX₁ : X₁.1 = Ti * e + mi * f + g := rfl
  refine ⟨s, ⟨?_, ?_⟩, ?_, ?_⟩
  · refine ⟨(T * e, mm), ⟨⟨⟨?_, ?_⟩, ?_⟩, ⟨m, hmM, rfl⟩⟩, hX₀.symm⟩
    · exact memR' _ (xT * (1 - xf - xg)).2
    · have : xT * (1 - xf - xg) * (1 - xf - xg) = xT * (1 - xf - xg) := by linear_combination xT * heR
      exact congrArg Subtype.val this
    · refine ⟨mm, ⟨m, hmM, rfl⟩, ?_⟩
      have : xT * xTp * (1 - xf - xg) = xT * (1 - xf - xg) * ((1 - xg - xf) * xTp) := by
        linear_combination (-(xT * xTp)) * heR
      have h2 := congrArg Subtype.val this
      show mm * e = T * e * star (T * e)
      rw [star_mul, hes, ← hm]
      exact h2
  · refine ⟨(Ti * e, mi), ⟨⟨⟨?_, ?_⟩, ?_⟩, ⟨m, hmM, rfl⟩⟩, hX₁.symm⟩
    · exact memR' _ (xTi * (1 - xf - xg)).2
    · have : xTi * (1 - xf - xg) * (1 - xf - xg) = xTi * (1 - xf - xg) := by linear_combination xTi * heR
      exact congrArg Subtype.val this
    · refine ⟨mi, ⟨m, hmM, rfl⟩, ?_⟩
      have hTT : xTi * xTip = xmi := by
        linear_combination (-(xTi * xTip)) * hmiR + xmi * xTp * xTip * hTiR + xmi * hTpiR
      have : xmi * (1 - xf - xg) = xTi * (1 - xf - xg) * ((1 - xg - xf) * xTip) := by
        linear_combination (-(xTi * xTip)) * heR - (1 - xf - xg) * hTT
      have h2 := congrArg Subtype.val this
      show mi * e = Ti * e * star (Ti * e)
      rw [star_mul, hes]
      exact h2
  · exact memR' _ X₀.2
  · have : X₀ * ((1 - xg - xf) * xTp + xg * (xT * xTp) + xf) = xT * xTp := by
      linear_combination xT * xTp * heR + xT ^ 2 * xTp * hegR + xT * hefR + xT * xTp ^ 2 * hefR +
        xT ^ 2 * xTp ^ 2 * hfgR + xT * xTp * hfR + xTp * hegR + xT * xTp * hgR + hfgR
    have h2 := congrArg Subtype.val this
    have hst : star X₀.1 = ((1 - xg - xf) * xTp + xg * (xT * xTp) + xf).1 := by
      show star (T * (1 - f - g) + T * star T * f + g) = (1 - g - f) * star T + g * (T * star T) + f
      rw [hg]
      simp only [star_add, star_mul, star_sub, star_one, star_star]
    show X₀.1 * star X₀.1 = T * star T
    rw [hst]
    exact h2

end GlobalTheory.NormSec
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCompactPreimageNormCentralizerHermitianStatement

section

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.exists_compact_preimage_norm_centralizer_hermitian : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (A₀ : Matrix (Fin r) (Fin r) E), A₀.IsHermitian → A₀.charpoly.Separable → ∀ M : Set (GL (Fin r) E), IsCompact M → ∃ S : Set (GL (Fin r) E), IsCompact S ∧ ∀ t : GL (Fin r) E, (t : Matrix (Fin r) (Fin r) E) * A₀ = A₀ * (t : Matrix (Fin r) (Fin r) E) → (∃ m ∈ M, (t : Matrix (Fin r) (Fin r) E) * star (t : Matrix (Fin r) (Fin r) E) = (m : Matrix (Fin r) (Fin r) E)) → ∃ s ∈ S, (s : Matrix (Fin r) (Fin r) E) * A₀ = A₀ * (s : Matrix (Fin r) (Fin r) E) ∧ (s : Matrix (Fin r) (Fin r) E) * star (s : Matrix (Fin r) (Fin r) E) = (t : Matrix (Fin r) (Fin r) E) * star (t : Matrix (Fin r) (Fin r) E) := by
  first | exact @GlobalTheory.NormSec.normsec | exact GlobalTheory.NormSec.normsec | (intros; apply GlobalTheory.NormSec.normsec <;> assumption)
end
end
