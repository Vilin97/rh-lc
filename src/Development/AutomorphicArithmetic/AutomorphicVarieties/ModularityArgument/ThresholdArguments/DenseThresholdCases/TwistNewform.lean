module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.TwNewQ
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SphericalDecomposition.SphOfWit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.KwAbs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.AdmissibleTwistByDet
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.NewformTwistNorms.NewformNormCoeffPrimeLeOfNotDvdLevel
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.NewformTwistNorms.PowEqOneOfKills
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicFormHyp
public import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.NewformTwistNorms.NewformOfAdmissibleTwist
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.UnramifiedAlgebraicWeights
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.NewformTwistNorms.NewformUnitRootNotRootOfUnityOddWeight

section

@[expose] public section

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2

theorem norm_eq_one_of_pow_eq_one' {R : Type} [NormedDivisionRing R] {z : R} {n : ℕ} (hn : 0 < n)
    (h : z ^ n = 1) : ‖z‖ = 1 := by
  have h1 : ‖z‖ ^ n = 1 := by rw [← norm_pow, h, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg z) hn.ne').1 h1

theorem dirichlet_pow_card_eq_one {M : ℕ} (hM : 0 < M) (χ : DirichletCharacter ℂ M) (l : ℕ) (h : l.Coprime M) :
    ∃ n : ℕ, 0 < n ∧ χ (l : ZMod M) ^ n = 1 := by
  haveI : NeZero M := ⟨hM.ne'⟩
  refine ⟨Fintype.card (ZMod M)ˣ, Fintype.card_pos, ?_⟩
  rw [← ZMod.coe_unitOfCoprime l h, ← map_pow, ← Units.val_pow_eq_pow_val, pow_card_eq_one, Units.val_one,
    map_one]

theorem hecke_gap (L : ℝ) (hL : 3 ≤ L) (e : ℕ) (he : 1 ≤ e) :
    L ^ (((2 * e + 1 : ℕ) : ℝ) / 2) + L ^ (((2 * e + 1 : ℕ) : ℝ) / 2 - 1) < L ^ (2 * e) - 1 := by
  have hL0 : 0 < L := by linarith
  set s := Real.sqrt L with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg L
  have hss : s * s = L := Real.mul_self_sqrt hL0.le
  have h1 : L ^ (((2 * e + 1 : ℕ) : ℝ) / 2) = L ^ e * s := by
    rw [hs, Real.sqrt_eq_rpow, ← Real.rpow_natCast L e, ← Real.rpow_add hL0]
    congr 1; push_cast; ring
  have h2 : L ^ (((2 * e + 1 : ℕ) : ℝ) / 2 - 1) = L ^ e * s / L := by
    rw [Real.rpow_sub hL0, Real.rpow_one, h1]
  rw [h1, h2]
  set N := L ^ e with hN
  have hNL : L ≤ N := by
    rw [hN]; calc L = L ^ 1 := (pow_one L).symm
      _ ≤ L ^ e := pow_le_pow_right₀ (by linarith) he
  have hsL : s < L - 1 := by nlinarith
  have key : N * s * (L + 1) < L * (N ^ 2 - 1) := by
    nlinarith [mul_nonneg (sub_nonneg.2 hNL) (show 0 ≤ L * (N + L) - (L + 1) * s by nlinarith),
      mul_pos (mul_pos (show (0:ℝ) < L + 1 by linarith) hL0) (show 0 < L - 1 - s by linarith)]
  have : N * s + N * s / L = N * s * (L + 1) / L := by field_simp
  rw [this, div_lt_iff₀ hL0]
  have : L ^ (2 * e) = N ^ 2 := by rw [hN, ← pow_mul, mul_comm]
  rw [this]; linarith

theorem heckePoly_root_eq {k : ℕ} (g : Newform k) (p : ℕ) (α : ℂ) (h : (g.heckePoly p).IsRoot α) :
    g.a p * α = α ^ 2 + g.χ (p : ZMod g.M) * (p : ℂ) ^ (k - 1) := by
  have := h.eq_zero
  simp only [Newform.heckePoly, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_mul, Polynomial.eval_C] at this
  linear_combination -this

theorem root_facts_of_bound
    (hbd : ∀ (k : ℕ) (g : Newform k) (p : ℕ), p.Prime → ¬ p ∣ g.M →
      ‖g.a p‖ ≤ (p : ℝ) ^ ((k : ℝ) / 2) + (p : ℝ) ^ ((k : ℝ) / 2 - 1)) :
    ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (e : ℕ) (g : Newform (2 * e + 1)) (α : ℂ), l ≠ 2 → 1 ≤ e → ¬ l ∣ g.M →
      (g.heckePoly l).IsRoot α → ‖ι.symm α‖ = 1 → ‖ι.symm (g.a l)‖ = 1 ∧ ∀ m : ℕ, 1 ≤ m → α ^ m ≠ 1 := by
  intro l _ ι e g α hl2 he hdiv hroot hα
  have hp : l.Prime := Fact.out
  have hcop : l.Coprime g.M := (Nat.Prime.coprime_iff_not_dvd hp).2 hdiv
  obtain ⟨n, hn, hχn⟩ := dirichlet_pow_card_eq_one g.pos g.χ l hcop
  have hrel := heckePoly_root_eq g l α hroot
  have hk : 2 * e + 1 - 1 = 2 * e := by omega
  rw [hk] at hrel
  set c := g.χ (l : ZMod g.M) with hc
  have hα0 : α ≠ 0 := by
    rintro rfl; simp at hα
  refine ⟨?_, ?_⟩
  ·
    have hA0 : ι.symm α ≠ 0 := by rw [Ne, map_eq_zero_iff _ ι.symm.injective]; exact hα0
    have hrel' : ι.symm (g.a l) = ι.symm α + ι.symm c * (l : Qbar l) ^ (2 * e) / ι.symm α := by
      field_simp
      have := congrArg ι.symm hrel
      simp only [map_mul, map_add (f := _), map_pow, map_natCast] at this
      linear_combination this
    have hcn : ‖ι.symm c‖ = 1 :=
      norm_eq_one_of_pow_eq_one' hn (by rw [← map_pow, hχn, map_one])
    have hln : ‖(l : Qbar l)‖ < 1 := by
      have h : ((l : ℕ) : Qbar l) = algebraMap ℚ_[l] (Qbar l) (l : ℚ_[l]) := by simp
      rw [h, PadicAlgCl.norm_extends]; exact Padic.norm_p_lt_one
    have hB : ‖ι.symm c * (l : Qbar l) ^ (2 * e) / ι.symm α‖ < 1 := by
      rw [norm_div, norm_mul, norm_pow, hcn, hα, one_mul, div_one]
      exact pow_lt_one₀ (norm_nonneg _) hln (by omega)
    rw [hrel', IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [hα]; exact hB.ne'), hα]
    exact max_eq_left hB.le
  ·
    intro m hm hαm
    have hαn : ‖α‖ = 1 := norm_eq_one_of_pow_eq_one' hm hαm
    have hcn : ‖c‖ = 1 := norm_eq_one_of_pow_eq_one' hn hχn
    have hb := hbd (2 * e + 1) g l hp hdiv
    have ha : g.a l = α + c * (l : ℂ) ^ (2 * e) / α := by
      field_simp; linear_combination hrel
    have hlow : (l : ℝ) ^ (2 * e) - 1 ≤ ‖g.a l‖ := by
      have h1 : ‖c * (l : ℂ) ^ (2 * e) / α‖ = (l : ℝ) ^ (2 * e) := by
        rw [norm_div, norm_mul, norm_pow, hcn, hαn, one_mul, div_one, Complex.norm_natCast]
      have h2 := norm_sub_norm_le (c * (l : ℂ) ^ (2 * e) / α) (-α)
      rw [h1, norm_neg, hαn, sub_neg_eq_add, add_comm] at h2
      rw [ha]; exact h2
    have hl3 : (3 : ℝ) ≤ l := by
      have := hp.two_le
      have : 3 ≤ l := by omega
      exact_mod_cast this
    have := hecke_gap (l : ℝ) hl3 e he
    linarith

theorem root_facts :
    ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (e : ℕ) (g : Newform (2 * e + 1)) (α : ℂ), l ≠ 2 → 1 ≤ e → ¬ l ∣ g.M →
      (g.heckePoly l).IsRoot α → ‖ι.symm α‖ = 1 → ‖ι.symm (g.a l)‖ = 1 ∧ ∀ m : ℕ, 1 ≤ m → α ^ m ≠ 1 :=
  root_facts_of_bound GlobalTheory.T.newform_norm_coeff_prime_le_of_not_dvd_level

end GlobalTheory.Ord2

end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

theorem _root_.GlobalTheory.T.newform_unit_root_not_root_of_unity_odd_weight : ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (e : ℕ) (g : Newform (2 * e + 1)) (α : ℂ), l ≠ 2 → 1 ≤ e → ¬ l ∣ g.M → (g.heckePoly l).IsRoot α → ‖ι.symm α‖ = 1 → ‖ι.symm (g.a l)‖ = 1 ∧ ∀ m : ℕ, 1 ≤ m → α ^ m ≠ 1 := by
  first | exact @GlobalTheory.Ord2.root_facts | exact GlobalTheory.Ord2.root_facts | (intros; apply GlobalTheory.Ord2.root_facts <;> assumption)

end
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ExistsRep

section

@[expose] public section




section
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
noncomputable section
open Polynomial Pointwise
namespace GlobalTheory.Ord2.SrcForm
open TwDet
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]
theorem exists_rep_alt (P : _root_.UpperTheory.V.Af.Hypotheses') [IsAlgClosure ℚ Ω] {k : ℕ} (hk : 2 ≤ k) (f : Newform k) (ι : Qbar l ≃+* ℂ) (W : R2 Ω l) (j : ℤ)
    (hf : f.Att ι (tw W (cycBar ℚ Ω l ^ j))) :
    ∃ π : TR.CuspSub ℚ 2, π.IsRegAlg ∧ AttR ι W π ∧ ∀ᶠ w : Pl in Filter.cofinite, ∃ Bs, π.HasSat w Bs ∧
      ((algSat 2 (normV w) Bs).map fun b => X - C ((normV w : ℂ) ^ (-j) * b)).prod = f.heckePoly (normV w) := by
  have hl : Fact l.Prime := inferInstance
  obtain ⟨π, hinf, hsat⟩ := P.newform k hk f (-j)
  refine ⟨π, fun v => ⟨_, hinf v, ?_, ?_⟩, ⟨ss_of_tw _ _ hf.1, ?_⟩, ?_⟩
  · simp only [Multiset.insert_eq_cons, Multiset.nodup_cons, Multiset.mem_singleton, Multiset.nodup_singleton, and_true]
    intro h
    have h1 : (k : ℂ) = 1 := by linear_combination h
    have h2 : k = 1 := by exact_mod_cast h1
    omega
  · intro z hz
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact ⟨-j, by push_cast; ring⟩
    · exact ⟨1 - k - j, by push_cast; ring⟩
  · filter_upwards [hf.2, ev_not_mem l hl.out.ne_zero, ev_not_mem f.M f.pos.ne'] with w hw hwl hwM
    obtain ⟨B, hB, hpoly⟩ := hsat w (not_dvd_of_not_mem hwM)
    refine ⟨B, hB, fun A hA => ⟨fun s hs => ?_, fun σ hσ => ?_⟩⟩
    · have h1 := (hw A hA).1 s hs
      have h2 : cycZ ℚ Ω l s = 1 := by
        refine Units.ext (PadicInt.ext_of_toZModPow.mp fun n => ?_)
        rw [cycZ_toZModPow_eq (v := w) (σ := s) hwl hA (q := 1) (fun x hx => by simpa only [pow_one] using hs.2 x hx) n]
        simp
      have h3 : (cycBar ℚ Ω l ^ j) s = 1 := by
        rw [MonoidHom.zpow_apply, cycBar, MonoidHom.comp_apply, h2, map_one, one_zpow]
      apply Units.ext
      have h4 := congrArg Units.val h1
      rwa [tw_val, h3, Units.val_one, one_smul] at h4
    · have h1 := (hw A hA).2 σ hσ
      rw [tw_val, ← hpoly] at h1
      refine scale_charpoly ι.toRingHom _ _ (Units.ne_zero ((cycBar ℚ Ω l ^ j) σ⁻¹)) _ ?_
      rw [h1]
      have h2 : ((cycBar ℚ Ω l σ : (Qbar l)ˣ) : Qbar l) = (normV w : ℕ) := by
        change algebraMap ℚ_[l] (Qbar l) (PadicInt.Coe.ringHom ((cycZ ℚ Ω l σ : ℤ_[l]ˣ) : ℤ_[l])) = _
        rw [cycZ_of_isFrob hwl hA hσ, map_natCast, map_natCast]
      have h3 : ι.toRingHom (((cycBar ℚ Ω l ^ j) σ⁻¹ : (Qbar l)ˣ) : Qbar l) = (normV w : ℂ) ^ (-j) := by
        rw [MonoidHom.zpow_apply, map_inv, Units.val_zpow_eq_zpow_val, Units.val_inv_eq_inv_val, h2, map_zpow₀,
          map_inv₀, map_natCast, inv_zpow']
      rw [h3]
  · filter_upwards [ev_not_mem f.M f.pos.ne'] with w hwM
    exact hsat w (not_dvd_of_not_mem hwM)
end GlobalTheory.Ord2.SrcForm
namespace GlobalTheory.Ord2
open TwDet SrcForm
end GlobalTheory.Ord2
end
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TwistNewform

section

@[expose] public section




section
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
open Polynomial Pointwise
namespace GlobalTheory.Ord2
open TwDet SrcForm
private theorem sources_of_spherical (P : _root_.UpperTheory.V.Af.HypothesesH') (hT : TwNewQ) (hF : UpperTheory.V.Z.Kato.WeilSphericalRecords.FrobRoot) (l : ℕ) [hl : Fact l.Prime] (Ω : Type) [Field Ω]
    [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ) (W : R2 Ω l) (hl2 : l ≠ 2) (he : 1 ≤ e) (h : admitted ι e W)
    (hS : UpperTheory.V.Z.Kato.SphAt ι e W) : GlobalTheory.Ord2.SrcL ι e W := by
  have hl0 : 0 < l := hl.out.pos
  obtain ⟨N, hN, hNk⟩ := UpperTheory.V.CF.kwAbs Ω (dt W).ker (ker_open h.cont h.det2)
    (Abelianization.commutator_subset_ker (dt W))
  have hθN : KillsMu N (dt W) := fun s hs => hNk s hs
  obtain ⟨A, χ, κ, hA, hχ, hfl, hine, hk⟩ := h.flag
  set φ : G ℚ Ω →* (Qbar l)ˣ := (dt W)⁻¹ * χ⁻¹ with hφdef
  have hNl : 0 < N * l := Nat.mul_pos hN hl0
  have hφ : KillsMu (N * l) φ :=
    killsMu_mul (killsMu_dvd (kills_inv hθN) (dvd_mul_right N l)) (killsMu_dvd (kills_inv hχ) (dvd_mul_left l N))
  obtain ⟨g, hg⟩ := hT l Ω ι e W hl2 he h (N * l) φ hNl hφ
  have hVc : Continuous (tw W φ) := tw_cont h.cont (cont_of_kills hNl hφ)
  have hVi : IsIrr (tw W φ) := irr_tw W φ _ h.irr
  have hVa : ∃ M : ℕ, 1 ≤ M ∧ LevelAway l M (tw W φ) := by
    obtain ⟨M, hM, hlev⟩ := h.away
    refine ⟨M * (N * l), Nat.mul_pos hM hNl, fun w hw => ?_⟩
    obtain ⟨B, hB, ψ, hψ, hd⟩ := hlev w hw
    exact ⟨B, hB, fun i => ψ i * φ, fun i => killsMu_mul (killsMu_dvd (hψ i) (dvd_mul_right _ _))
      (killsMu_dvd hφ (dvd_mul_left _ _)), diag_twist φ hd⟩
  have hVd : ∃ M : ℕ, 1 ≤ M ∧ KillsMu M (dt (tw W φ)) := by
    refine ⟨N * l, hNl, ?_⟩
    rw [dt_tw, pow_two]
    exact killsMu_mul (killsMu_mul hφ hφ) (killsMu_dvd hθN (dvd_mul_right N l))
  have hVf := flag_twist φ hfl
  have hVk : ∀ s : ↥(Dec (F := ℚ) A), (s : G ℚ Ω) ∈ Ine (F := ℚ) A →
      (κ 0 * φ.comp (Dec (F := ℚ) A).subtype) s = cycBar ℚ Ω l s ^ (e : ℤ) ∧
      (κ 1 * φ.comp (Dec (F := ℚ) A).subtype) s = cycBar ℚ Ω l s ^ (-(e : ℤ)) := by
    intro s hs
    have h1 : dt W (s : G ℚ Ω) = 1 := hine hs
    obtain ⟨h0, h1'⟩ := hk s hs
    simp only [hφdef, MonoidHom.mul_apply, MonoidHom.comp_apply, MonoidHom.inv_apply, Subgroup.coe_subtype, h1, inv_one,
      one_mul, h0, h1', mul_inv_cancel_right, and_self]
  obtain ⟨π, hreg, hatt, hsat⟩ := _root_.GlobalTheory.Ord2.SrcForm.exists_rep_alt P.toClassicalTheorems (by omega) g ι (tw W φ) (-(e : ℤ)) hg
  obtain ⟨v, hv, hlv⟩ := id hA
  have hnv : normV v = l := normV_of_mem hl.out hlv
  obtain ⟨Bs, hBs⟩ := hS (N * l) φ hNl hφ A v _ hv hlv hVf hVk π hreg hatt
  have hlev : ¬ l ∣ g.M := hnv ▸ _root_.GlobalTheory.NewLevel.not_dvd_level_of_satake_hecke_poly_cofinite P.toClassicalTheorems P.ssR _ (by omega) g _ π hsat v Bs hBs
  obtain ⟨σ, hσ⟩ := exists_isFrob (Ω := Ω) hv
  rw [hnv] at hσ
  obtain ⟨α, hroot, hα⟩ := hF l Ω ι e (tw W φ) A _ g hl2 he hVc hVi hVd hA ⟨hVf, hVk⟩ hg hlev ⟨σ, hσ.1⟩ hσ
  set u : (Qbar l)ˣ := (κ 0 * φ.comp (Dec (F := ℚ) A).subtype) ⟨σ, hσ.1⟩ * cycBar ℚ Ω l σ ^ (-(e : ℤ)) with hu
  have hun : ‖(u : Qbar l)‖ = 1 := by
    rw [hu, Units.val_mul, norm_mul, norm_flag hVc hVf 0, Units.val_zpow_eq_zpow_val, norm_zpow, norm_cyc, one_zpow, one_mul]
  have hα' : α = ι (u : Qbar l) ∨ α = (ι (u : Qbar l))⁻¹ := hα.imp id fun h => by rw [← h, inv_inv]
  have hαn : ‖ι.symm α‖ = 1 := by
    rcases hα' with h1 | h1
    · rw [h1, RingEquiv.symm_apply_apply, hun]
    · rw [h1, map_inv₀, RingEquiv.symm_apply_apply, norm_inv, hun, inv_one]
  obtain ⟨hal, hpow⟩ := GlobalTheory.T.newform_unit_root_not_root_of_unity_odd_weight l ι e g α hl2 he hlev hroot hαn
  refine ⟨⟨g, χ⁻¹, A, κ, hlev, hal, kills_inv hχ, ?_, hA, hfl, fun s hs => ?_⟩, fun A' κ' hA' hfl' => ?_⟩
  · rw [tw_tw] at hg
    rw [mul_assoc]
    exact hg
  · have h1 : dt W (s : G ℚ Ω) = 1 := hine hs
    have h2 : (cycBar ℚ Ω l (s : G ℚ Ω) : Qbar l) ≠ 0 := Units.ne_zero _
    have h3 : (χ (s : G ℚ Ω) : Qbar l) ≠ 0 := Units.ne_zero _
    have h4 : (cycBar ℚ Ω l (s : G ℚ Ω) : Qbar l) ^ (e : ℤ) ≠ 0 := zpow_ne_zero _ h2
    rw [(hk s hs).2, h1, MonoidHom.inv_apply, Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_inv_eq_inv_val,
      Units.val_one, inv_one, one_mul, zpow_neg]
    field_simp
  · by_contra hn
    push Not at hn
    obtain ⟨m, hm, hχm⟩ := pow_eq_one_of_kills hl0 hχ
    obtain ⟨t, ht, htk⟩ := cyc_inf hA
    obtain ⟨h0, h1⟩ := hk ⟨t, Ine_le_Dec A ht⟩ ht
    rcases eps_mem hA hA' hfl hfl' hn with hc | hc
    · rw [← hc] at h0
      simp only at h0
      have he1 : e = 1 := by
        by_contra hne
        obtain ⟨d, rfl⟩ : ∃ d, e = d + 1 := ⟨e - 1, by omega⟩
        refine htk (d * m) (Nat.mul_ne_zero (by omega) (by omega)) ?_
        have h2 : cycBar ℚ Ω l t ^ d * χ t = 1 := by
          rw [zpow_natCast, pow_succ', mul_assoc] at h0
          exact (left_eq_mul.1 h0)
        rw [pow_mul, eq_inv_of_mul_eq_one_left h2, inv_pow, hχm, inv_one]
      obtain ⟨m', hm', hφm⟩ := pow_eq_one_of_kills hNl hφ
      have hu' : u = φ σ := by
        rw [hu, MonoidHom.mul_apply, ← hc, he1]
        simp [mul_inv_cancel_comm]
      have hu1 : ι (u : Qbar l) ^ m' = 1 := by
        rw [← map_pow, ← Units.val_pow_eq_pow_val, hu', hφm, Units.val_one, map_one]
      refine hpow m' hm' ?_
      rcases hα' with h1 | h1
      · rw [h1, hu1]
      · rw [h1, inv_pow, hu1, inv_one]
    · rw [← hc] at h1
      simp only at h1
      refine htk ((e + 1) * m) (Nat.mul_ne_zero (by omega) (by omega)) ?_
      have h2 : cycBar ℚ Ω l t ^ (e + 1) = χ t := by
        rw [pow_succ]
        nth_rewrite 2 [h1]
        rw [zpow_neg, zpow_natCast, mul_inv_cancel_left]
      rw [pow_mul, h2, hχm]
end GlobalTheory.Ord2
end
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Z.Win UpperTheory.V.Z.Kato UpperTheory.V.Z.Kato.WeilSphericalRecords UpperTheory.Zero.LLC
theorem UpperTheory.V.Z.Kato.WeilSphericalRecords.srcS_alt :
    _root_.UpperTheory.V.Af.HypothesesH' → GlobalTheory.Ord2.TwNewQ → FrobRoot → SrcS :=
  fun P hT hF l _ Ω _ _ _ ι e W hl he hW hS => GlobalTheory.Ord2.sources_of_spherical P hT hF l Ω ι e W hl he hW hS
end
end
end
