module

public import Development.AbelianVarietyTheory.Definitions.Divisors.UnipVal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantAddChar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuadExtTopologyStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactOpenNormClosedBallQuadraticStatement
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryCharacterAbsScalarEventuallyEqOne

section

@[expose] public section

noncomputable section

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary ValuativeRel Filter
open scoped Topology
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

namespace GlobalTheory.KSp

theorem sc_eventually_eq_one : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E]
    (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (m : ℕ) (χ : Eˣ →* Circle) (_ : Continuous χ),
    ∀ᶠ z in nhds (1 : E), sc F χ m z = 1 := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE m χ hχ
  obtain ⟨hfd, htr, hinv, ht2, -, hN, -, -⟩ := GlobalTheory.T.quadExt_topological_properties F E c δ hE
  obtain ⟨L, hL, hLc, hLo⟩ := GlobalTheory.T.exists_compactOpen_normClosedBall_quadratic F E c δ hE 1

  have h0 : {t : Eˣ | ‖(χ t : ℂ) - 1‖ < 1 / 2} ∈ 𝓝 (1 : Eˣ) :=
    (isOpen_lt (by fun_prop) continuous_const).mem_nhds (by simp)
  rw [Units.isEmbedding_val₀.nhds_eq_comap, mem_comap] at h0
  obtain ⟨U, hU, hUV⟩ := h0

  have h1 : ∀ᶠ π in 𝓝 (0 : F), ∀ a ∈ (L : Set E), 1 + π • a ∈ U := by
    refine hLc.eventually_forall_of_forall_eventually fun a _ => ?_
    have : Tendsto (fun q : F × E => 1 + q.1 • q.2) (𝓝 (0, a)) (𝓝 1) :=
      Continuous.tendsto' (by fun_prop) _ _ (by simp)
    exact this hU
  have h2 : {x : F | valuation F x < 1} ∈ 𝓝 (0 : F) := (IsValuativeTopology.mem_nhds_zero_iff _).mpr ⟨1, fun _ h => h⟩
  obtain ⟨s, hs⟩ := GlobalTheory.SplitWeil.exists_cball_subset (inter_mem h1 h2)
  obtain ⟨hsU, hsv⟩ := hs (show (s : F) ∈ GlobalTheory.SplitWeil.cball s from show valuation F (s : F) ≤ valuation F (s : F) from le_rfl)
  set π : F := (s : F) with hπdef
  have hπ : π ≠ 0 := s.ne_zero

  have hmul : ∀ a ∈ (L : Set E), ∀ b ∈ (L : Set E), a * b ∈ (L : Set E) := by
    intro a ha b hb
    rw [hL] at ha hb ⊢
    show valuation F (Algebra.norm F (a * b)) ≤ valuation F ((1 : Fˣ) : F)
    have ha' : valuation F (Algebra.norm F a) ≤ 1 := by simpa [GlobalTheory.SplitWeil.cball] using ha
    have hb' : valuation F (Algebra.norm F b) ≤ 1 := by simpa [GlobalTheory.SplitWeil.cball] using hb
    rw [map_mul, map_mul]
    simpa using mul_le_one' ha' hb'
  have hsm : ∀ a ∈ (L : Set E), π • a ∈ (L : Set E) := by
    intro a ha
    rw [hL] at ha ⊢
    show valuation F (Algebra.norm F (π • a)) ≤ valuation F ((1 : Fˣ) : F)
    have ha' : valuation F (Algebra.norm F a) ≤ 1 := by simpa [GlobalTheory.SplitWeil.cball] using ha
    rw [Algebra.smul_def, map_mul, Algebra.norm_algebraMap, map_mul, map_pow]
    simpa using mul_le_one' (pow_le_one' hsv.le _) ha'

  set V : Set E := {z | π⁻¹ • (z - 1) ∈ (L : Set E)} with hVdef
  have hVo : IsOpen V := hLo.preimage (by fun_prop)
  have hV1 : (1 : E) ∈ V := by simp [V, L.zero_mem]
  have hVU : V ⊆ U := by
    intro z hz
    have := hsU _ hz
    rwa [smul_smul, mul_inv_cancel₀ hπ, one_smul, add_sub_cancel] at this
  have hVpow : ∀ z ∈ V, ∀ n : ℕ, z ^ n ∈ V := by
    intro z hz n
    induction n with
    | zero => simpa using hV1
    | succ n ih =>
      show π⁻¹ • (z ^ (n + 1) - 1) ∈ (L : Set E)
      have hz' : z = 1 + π • (π⁻¹ • (z - 1)) := by
        rw [smul_smul, mul_inv_cancel₀ hπ, one_smul, add_sub_cancel]
      have e : π⁻¹ • (z ^ (n + 1) - 1) =
          π⁻¹ • (z ^ n - 1) + π • ((π⁻¹ • (z - 1)) * (π⁻¹ • (z ^ n - 1))) + π⁻¹ • (z - 1) := by
        have hp : algebraMap F E π ≠ 0 := (map_ne_zero _).mpr hπ
        simp only [Algebra.smul_def, map_inv₀]
        field_simp
        ring
      rw [e]
      exact L.add_mem (L.add_mem ih (hsm _ (hmul _ hz _ ih))) hz

  have h3 : Tendsto (fun z : E => Algebra.norm F z - 1) (𝓝 1) (𝓝 0) :=
    Continuous.tendsto' (by fun_prop) _ _ (by simp)
  filter_upwards [hVo.mem_nhds hV1, eventually_ne_nhds (one_ne_zero : (1 : E) ≠ 0), h3.eventually h2] with z hz hz0 hzN
  have hv : valuation F (Algebra.norm F z) = 1 := by
    simpa using (valuation F).map_one_add_of_lt hzN
  have hχz : χ (Units.mk0 z hz0) = 1 := by
    refine Circle.coe_eq_one.mp (GlobalTheory.WeilM.eq_one_of_forall_pow_near fun n => ?_)
    have : (Units.mk0 z hz0) ^ n ∈ Units.val ⁻¹' U := by simpa using hVU (hVpow z hz n)
    simpa using hUV this
  have hn : nabs F (Units.map (Algebra.norm F : E →* F) (Units.mk0 z hz0)) = 1 :=
    GlobalTheory.SplitWeil.nabs_eq_one_of_valuation_eq_one (by simpa using hv)
  simp [sc, hz0, hχz, hn]

end GlobalTheory.KSp

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryCharacterAbsScalarEventuallyEqOneStatement

section

@[expose] public section

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

theorem _root_.GlobalTheory.T.unitaryCharacterAbsScalar_eventually_eq_one : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (m : ℕ) (χ : Eˣ →* Circle) (_ : Continuous χ), ∀ᶠ z in nhds (1 : E), sc F χ m z = 1 := by
  first | exact @GlobalTheory.KSp.sc_eventually_eq_one | exact GlobalTheory.KSp.sc_eventually_eq_one | (intros; apply GlobalTheory.KSp.sc_eventually_eq_one <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatFixedNearOneSiegelParabolic

section

@[expose] public section

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
open Filter Topology

namespace GlobalTheory.KSp.ParNear

variable {E : Type} [Field E] {ν : Type} [Fintype ν] [DecidableEq ν]

theorem toBlocks₁₁_mul_of_toBlocks₂₁_eq_zero (M N : Matrix (ν ⊕ ν) (ν ⊕ ν) E) (h : N.toBlocks₂₁ = 0) :
    (M * N).toBlocks₁₁ = M.toBlocks₁₁ * N.toBlocks₁₁ := by
  rw [← fromBlocks_toBlocks M, ← fromBlocks_toBlocks N, h, fromBlocks_multiply]
  simp

theorem toBlocks₁₁_one' : (1 : Matrix (ν ⊕ ν) (ν ⊕ ν) E).toBlocks₁₁ = 1 := by
  ext i j; simp [toBlocks₁₁, Matrix.one_apply]

theorem toBlocks₁₂_one' : (1 : Matrix (ν ⊕ ν) (ν ⊕ ν) E).toBlocks₁₂ = 0 := by
  ext i j; simp [toBlocks₁₂, one_apply]

variable {F : Type} [Field F] [Algebra F E] (c : E →ₐ[F] E) {α : Type} [Fintype α] [DecidableEq α]

theorem mat_one : mat c (1 : UG c (stdJ ν E)) = 1 := rfl

theorem mat_mul_mat_inv (g : UG c (stdJ ν E)) : mat c g * mat c g⁻¹ = 1 := by
  change (((g * g⁻¹ : UG c (stdJ ν E)) : GL (ν ⊕ ν) E) : Matrix (ν ⊕ ν) (ν ⊕ ν) E) = 1
  rw [mul_inv_cancel]; rfl

theorem pr_zero_right (Q : Matrix α α E) (x : Matrix α ν E) : pr c Q x 0 = 0 := by
  simp [pr, form, GlobalTheory.WeilM.hTens]

variable [TopologicalSpace F] [TopologicalSpace E] [IsTopologicalRing E]

theorem continuous_mat : Continuous fun g : UG c (stdJ ν E) => mat c g :=
  Units.continuous_val.comp continuous_subtype_val

theorem continuous_mat_inv : Continuous fun g : UG c (stdJ ν E) => mat c g⁻¹ :=
  Units.continuous_coe_inv.comp continuous_subtype_val

theorem continuous_pr (hc : Continuous c) (htr : Continuous (Algebra.trace F E)) [ContinuousMul F] (Q : Matrix α α E) :
    Continuous fun p : Matrix α ν E × Matrix α ν E => pr c Q p.1 p.2 := by
  simp only [pr, form, GlobalTheory.WeilM.hTens]
  refine continuous_const.mul (htr.comp (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    continuous_finsetSum _ fun k _ => continuous_finsetSum _ fun l _ => ?_))
  refine Continuous.mul (Continuous.mul (Continuous.mul ?_ continuous_const) continuous_const) (hc.comp ?_)
  · rcases j with j | j
    · exact continuous_fst.matrix_elem i j
    · exact continuous_const
  · rcases l with l | l
    · exact continuous_const
    · exact continuous_snd.matrix_elem k l

theorem continuous_pr_comp (hc : Continuous c) (htr : Continuous (Algebra.trace F E)) [ContinuousMul F] (Q : Matrix α α E)
    {X : Type} [TopologicalSpace X] {f g : X → Matrix α ν E} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun x => pr c Q (f x) (g x) := by
  have h := (continuous_pr (ν := ν) c hc htr Q).comp (hf.prodMk hg)
  exact h

end GlobalTheory.KSp.ParNear

theorem GlobalTheory.KSp.parFun_fixed_near_one : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) (χ : Eˣ →* Circle) (_ : Continuous χ) (_ : ResEtaPow (R := F) ⊥ χ (Fintype.card α)), ∀ φ ∈ SB (Matrix α ν E), ∀ᶠ g in nhds (1 : UG c (stdJ ν E)), g ∈ sieg c ν → parFun c ψ χ Q (mat c g) φ = φ := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE α _ _ ν _ _ Q _ ψ hψ _ _ χ hχ _ φ hφ
  obtain ⟨-, htop, -, -, hcc, -, htr, -⟩ := GlobalTheory.T.quadExt_topological_properties F E c δ hE
  haveI := htop
  haveI := GlobalTheory.WeilM.nonarch_field F
  have hψl := GlobalTheory.WeilM.isLocallyConstant_addChar ψ hψ
  have hφl : IsLocallyConstant φ := hφ.1
  have hK : IsCompact (tsupport φ) := hφ.2
  have hA : Continuous fun g : UG c (stdJ ν E) => (mat c g).toBlocks₁₁ :=
    continuous_pi fun i => continuous_pi fun j => (GlobalTheory.KSp.ParNear.continuous_mat c).matrix_elem _ _
  have hB : Continuous fun g : UG c (stdJ ν E) => (mat c g).toBlocks₁₂ :=
    continuous_pi fun i => continuous_pi fun j => (GlobalTheory.KSp.ParNear.continuous_mat c).matrix_elem _ _
  have hA' : Continuous fun g : UG c (stdJ ν E) => (mat c g⁻¹).toBlocks₁₁ :=
    continuous_pi fun i => continuous_pi fun j => (GlobalTheory.KSp.ParNear.continuous_mat_inv c).matrix_elem _ _

  have hi : ∀ᶠ g in 𝓝 (1 : UG c (stdJ ν E)), sc F χ (Fintype.card α) (mat c g).toBlocks₁₁.det = 1 := by
    have ht : Tendsto (fun g : UG c (stdJ ν E) => (mat c g).toBlocks₁₁.det) (𝓝 1) (𝓝 1) := by
      have := hA.matrix_det.tendsto 1
      rwa [GlobalTheory.KSp.ParNear.mat_one, GlobalTheory.KSp.ParNear.toBlocks₁₁_one', det_one] at this
    exact ht.eventually (GlobalTheory.T.unitaryCharacterAbsScalar_eventually_eq_one F E c δ hE _ χ hχ)

  have hii : ∀ᶠ g in 𝓝 (1 : UG c (stdJ ν E)), ∀ x ∈ tsupport φ,
      ψ (2⁻¹ * pr c Q (x * (mat c g).toBlocks₁₁) (x * (mat c g).toBlocks₁₂)) * φ (x * (mat c g).toBlocks₁₁) = φ x := by
    refine hK.eventually_forall_of_forall_eventually fun x _ => ?_
    have hP : Continuous fun p : UG c (stdJ ν E) × Matrix α ν E =>
        pr c Q (p.2 * (mat c p.1).toBlocks₁₁) (p.2 * (mat c p.1).toBlocks₁₂) :=
      GlobalTheory.KSp.ParNear.continuous_pr_comp c hcc htr Q (continuous_snd.matrix_mul (hA.comp continuous_fst))
        (continuous_snd.matrix_mul (hB.comp continuous_fst))
    have hP2 : Continuous fun p : UG c (stdJ ν E) × Matrix α ν E =>
        (2 : F)⁻¹ * pr c Q (p.2 * (mat c p.1).toBlocks₁₁) (p.2 * (mat c p.1).toBlocks₁₂) :=
      continuous_const.mul hP
    have h1 : IsLocallyConstant fun p : UG c (stdJ ν E) × Matrix α ν E =>
        ψ (2⁻¹ * pr c Q (p.2 * (mat c p.1).toBlocks₁₁) (p.2 * (mat c p.1).toBlocks₁₂)) :=
      hψl.comp_continuous hP2
    have h2 : IsLocallyConstant fun p : UG c (stdJ ν E) × Matrix α ν E => φ (p.2 * (mat c p.1).toBlocks₁₁) :=
      hφl.comp_continuous (continuous_snd.matrix_mul (hA.comp continuous_fst))
    have h3 : IsLocallyConstant fun p : UG c (stdJ ν E) × Matrix α ν E => φ p.2 :=
      hφl.comp_continuous continuous_snd
    filter_upwards [h1.eventually_eq (1, x), h2.eventually_eq (1, x), h3.eventually_eq (1, x)] with p e1 e2 e3
    rw [e1, e2, e3, GlobalTheory.KSp.ParNear.mat_one, GlobalTheory.KSp.ParNear.toBlocks₁₁_one', GlobalTheory.KSp.ParNear.toBlocks₁₂_one', Matrix.mul_one, Matrix.mul_zero,
      GlobalTheory.KSp.ParNear.pr_zero_right, mul_zero, AddChar.map_zero_eq_one, one_mul]

  have hiii : ∀ᶠ g in 𝓝 (1 : UG c (stdJ ν E)), ∀ y ∈ tsupport φ, φ (y * (mat c g⁻¹).toBlocks₁₁) = φ y := by
    refine hK.eventually_forall_of_forall_eventually fun y _ => ?_
    have h2 : IsLocallyConstant fun p : UG c (stdJ ν E) × Matrix α ν E => φ (p.2 * (mat c p.1⁻¹).toBlocks₁₁) :=
      hφl.comp_continuous (continuous_snd.matrix_mul (hA'.comp continuous_fst))
    have h3 : IsLocallyConstant fun p : UG c (stdJ ν E) × Matrix α ν E => φ p.2 :=
      hφl.comp_continuous continuous_snd
    filter_upwards [h2.eventually_eq (1, y), h3.eventually_eq (1, y)] with p e2 e3
    rw [e2, e3, inv_one, GlobalTheory.KSp.ParNear.mat_one, GlobalTheory.KSp.ParNear.toBlocks₁₁_one', Matrix.mul_one]
  filter_upwards [hi, hii, hiii] with g hg1 hg2 hg3 hg
  have hinv : (mat c g).toBlocks₁₁ * (mat c g⁻¹).toBlocks₁₁ = 1 := by
    rw [← GlobalTheory.KSp.ParNear.toBlocks₁₁_mul_of_toBlocks₂₁_eq_zero _ _ ((GlobalTheory.KSp.mem_sieg c).mp ((sieg c ν).inv_mem hg)),
      GlobalTheory.KSp.ParNear.mat_mul_mat_inv, GlobalTheory.KSp.ParNear.toBlocks₁₁_one']
  funext x
  simp only [parFun]
  rw [hg1, one_mul]
  by_cases hx : x ∈ tsupport φ
  · exact hg2 x hx
  · rw [image_eq_zero_of_notMem_tsupport hx]
    by_contra hne
    have hne' : φ (x * (mat c g).toBlocks₁₁) ≠ 0 := right_ne_zero_of_mul hne
    have hy : x * (mat c g).toBlocks₁₁ ∈ tsupport φ := subset_tsupport _ hne'
    have e := hg3 _ hy
    rw [Matrix.mul_assoc, hinv, Matrix.mul_one] at e
    exact hx (subset_tsupport _ (by rw [Function.mem_support, e]; exact hne'))
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatFixedNearOneSiegelParabolicStatement

section

@[expose] public section

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

theorem _root_.GlobalTheory.T.schwartzBruhat_fixed_near_one_siegelParabolic : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) (χ : Eˣ →* Circle) (_ : Continuous χ) (_ : ResEtaPow (R := F) ⊥ χ (Fintype.card α)), ∀ φ ∈ SB (Matrix α ν E), ∀ᶠ g in nhds (1 : UG c (stdJ ν E)), g ∈ sieg c ν → parFun c ψ χ Q (mat c g) φ = φ := by
  first | exact @GlobalTheory.KSp.parFun_fixed_near_one | exact GlobalTheory.KSp.parFun_fixed_near_one | (intros; apply GlobalTheory.KSp.parFun_fixed_near_one <;> assumption)
end
end
