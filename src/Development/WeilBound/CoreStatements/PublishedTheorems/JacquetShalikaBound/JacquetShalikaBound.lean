module

public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaBound.FormQuasiInvariantMirabolic
public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaBound.lift_levelP_alt₂
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CMEqZeroOfNe
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoeffEqPowOfMulOneSub
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ColumnAverageHermitianPositive
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ColumnAverageQuasiInvariant
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ColumnMirabolicHolds
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousOfTrivialInteger
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsPowMulMemInteger
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsTranslateNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantHermitianFormCuspidalRep
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspRapidDecaySiegelGL
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalEqTwistNormalised
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUnitOfOneAdd
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.RingTheory.WittVector.IsPoly
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InvMulMemIntegralGLOfMem
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Linter.HaveILetI
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemUnipBOfMemUnipotent
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MinusculeSetEqDoubleCoset
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModulusEqOneOfIntegral
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrthogonalityOfLatticeCharacter
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondCountableField
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SumRangeEsymmLMulSchur
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SymmetricFunctionAbsoluteValues
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TendstoZeroOfSumSqLe
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedColumnAverageExists
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipCMemIntegralGL
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValuationLtOneOfDiv

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUnitForm

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.LFun PositivityTheory.JacquetShalikaLocal

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.JSUnit

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem norm_central (π : CuspSub E a) (H : π.V →ₗ⋆[ℂ] π.V →ₗ[ℂ] ℂ) (hp : ∀ φ, φ ≠ 0 → 0 < (H φ φ).re)
    (hi : ∀ k φ ψ, H (π.op (.fin k) φ) (π.op (.fin k) ψ) = H φ ψ) {ω : HChar E} (hω : π.HasCentChar ω) (z) :
    ‖((ω.1 (finId E z) : ℂˣ) : ℂ)‖ = 1 := by
  have := Submodule.nontrivial_iff_ne_bot.2 π.ne_bot
  obtain ⟨x, hx⟩ := exists_ne (0 : π.V)
  have h1 : π.op (.fin (GeneralLinearGroup.scalar (Fin a) z)) x = ((ω.1 (finId E z) : ℂˣ) : ℂ) • x := hω z x
  have h2 := hi (GeneralLinearGroup.scalar (Fin a) z) x x
  rw [h1] at h2
  generalize ((ω.1 (finId E z) : ℂˣ) : ℂ) = c at h2 ⊢
  simp only [map_smulₛₗ, map_smul, LinearMap.smul_apply, smul_eq_mul] at h2
  have hne : H x x ≠ 0 := fun e => by
    have h := hp x hx
    simp [e] at h
  have h3 : starRingEnd ℂ c * c = 1 := mul_right_cancel₀ hne (by linear_combination h2)
  rw [Complex.conj_mul'] at h3
  have h4 : ‖c‖ ^ 2 = 1 := by exact_mod_cast h3
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h4

theorem norm_loc (π : CuspSub E a) (H : π.V →ₗ⋆[ℂ] π.V →ₗ[ℂ] ℂ) (hp : ∀ φ, φ ≠ 0 → 0 < (H φ φ).re)
    (hi : ∀ k φ ψ, H (π.op (.fin k) φ) (π.op (.fin k) ψ) = H φ ψ) (χ : HChar E) {ω : HChar E} (hu : ω.IsUnitary)
    (hω : (π.twist χ).HasCentChar ω) (ha : a ≠ 0) (w : HeightOneSpectrum (𝓞 E)) (g : GL (Fin a) (w.adicCompletion E)) :
    ‖((χ.loc w (GeneralLinearGroup.det g) : ℂˣ) : ℂ)‖ = 1 := by
  have e : (π.twist χ).twist χ⁻¹ = π := by
    rw [← CuspSub.twist_mul, mul_inv_cancel, CuspSub.twist_one]
  have h2 := hω.twist χ⁻¹
  rw [e] at h2
  have h3 := norm_central π H hp hi h2 (GeneralLinearGroup.det (locGL E a w g))
  rw [finId_det_locGL] at h3
  generalize GeneralLinearGroup.det g = u at h3 ⊢
  have h4 : ‖((ω.loc w u : ℂˣ) : ℂ)‖ = 1 := hu _
  have h5 : (ω * χ⁻¹ ^ a).loc w u = ω.loc w u * (χ.loc w u)⁻¹ ^ a := rfl
  change ‖(((ω * χ⁻¹ ^ a).loc w u : ℂˣ) : ℂ)‖ = 1 at h3
  rw [h5] at h3
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, norm_mul, norm_pow, norm_inv, h4,
    one_mul] at h3
  have h6 := (pow_eq_one_iff_of_nonneg (by positivity) ha).1 h3
  exact inv_eq_one.1 h6

theorem exists_unit_form : G1 := by
  intro E _ _ _ a π hu w
  obtain ⟨ω, hωu, hω⟩ := hu
  rw [CG.hasCentChar_mk] at hω
  obtain ⟨π₀, χ, hn, rfl⟩ := GlobalTheory.CompanionTheory.TwistNorm.exists_twist_normalised π
  obtain ⟨H, h1, h2, h3, -, -⟩ := GlobalTheory.GelfandKazhdanHerm.exists_invariant_hermitian
    GlobalTheory.CompanionTheory.CuspFinGL.cuspFormsBoundedGL E a π₀ hn
  let T := π₀.toTwist χ
  have hT : ∀ g x, (π₀.twist χ).locRep w g (T x) =
      ((χ.loc w (GeneralLinearGroup.det g) : ℂˣ) : ℂ) • T (π₀.locRep w g x) := fun g x => by
    rw [CuspSub.locRep_eq, CuspSub.op_toTwist, opAdd, zero_smul, add_zero, map_smul, opMul, CuspSub.chiDet_locGL]
    rfl
  have hn1 : ∀ g : GL (Fin a) (w.adicCompletion E), ‖((χ.loc w (GeneralLinearGroup.det g) : ℂˣ) : ℂ)‖ = 1 := fun g => by
    rcases eq_or_ne a 0 with rfl | ha
    · rw [show GeneralLinearGroup.det g = 1 from Units.ext (by simp [Matrix.det_isEmpty]), map_one]
      simp
    · exact norm_loc π₀ H h2 h3 χ hωu hω ha w g
  refine ⟨(H.comp T.symm.toLinearMap).compl₂ T.symm.toLinearMap, ?_⟩
  refine And.intro (fun u v => ?_) (And.intro (fun u hu => ?_) fun g u v => ?_)
  · simpa using h1 (T.symm u) (T.symm v)
  · exact h2 _ (T.symm.map_ne_zero_iff.2 hu)
  · obtain ⟨u, rfl⟩ := T.surjective u
    obtain ⟨v, rfl⟩ := T.surjective v
    rw [hT, hT]
    generalize hc : ((χ.loc w (GeneralLinearGroup.det g) : ℂˣ) : ℂ) = c
    have hcc : starRingEnd ℂ c * c = 1 := by
      rw [Complex.conj_mul', ← hc, hn1 g]
      simp
    simp only [LinearMap.compl₂_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, map_smulₛₗ, map_smul, LinearMap.smul_apply,
      LinearEquiv.symm_apply_apply, smul_eq_mul]
    rw [CuspSub.locRep_eq, h3, ← mul_assoc, RingHom.id_apply, mul_comm c, hcc, one_mul]

end GlobalTheory.CompanionTheory.JSUnit

end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinalFormBesselBound

section

@[expose] public section

noncomputable section

open MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Iwasawa
  GroundTheory.Automorphic.Spherical PositivityTheory.JacquetShalikaLocal
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.SatakeBound

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {V : Type} [AddCommGroup V] [Module ℂ V]

theorem inv_top {n : ℕ} (hn : 1 < n) {ρ : Representation ℂ (GL (Fin n) F) V} {ψ : AddChar F ℂ}
    {l : V →ₗ[ℂ] ℂ} {B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ} (hU : Unit' ρ B) : Inv ρ ψ l (n - 1) B := by
  obtain ⟨hh, hp, hi⟩ := hU
  refine ⟨hh, fun u => ?_, fun u hu => ?_, fun g _ u u' => ?_, fun g hg u u' => ?_⟩
  · by_cases h : u = 0
    · simp [h]
    · exact (hp u h).le
  · by_cases h : u = 0
    · simp [h]
    · have := hp u h
      rw [hu] at this
      simp at this
  · rw [hi, Nat.sub_self, pow_zero, one_mul]
  · have h1 : g = 1 := by
      apply Units.ext
      ext i j
      exact hg.2 i j (by omega)
    subst h1
    rw [Whittaker.psiN_one]
    simp

theorem inv_step [MeasurableSpace F] [BorelSpace F] (h4a : StableAverageExists) (h4b : FormHermitianPositive) (h4c : FormQuasiInvariantMirabolic) (h4d : FormEquivariantColumn)
    (μ : Measure F) [μ.IsAddHaarMeasure] {ψ : AddChar F ℂ} (hψ : PsiOK ψ) {n : ℕ}
    {ρ : Representation ℂ (GL (Fin n) F) V} (hρ : Smooth ρ) {l : V →ₗ[ℂ] ℂ} (hW : Whit ρ ψ l)
    {k : ℕ} (hk : k + 1 < n) {B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ} (hB : Inv ρ ψ l (k + 1) B) :
    ∃ B', Char μ ρ ψ k B B' ∧ Inv ρ ψ l k B' := by
  obtain ⟨B', hC⟩ := h4a F μ ψ hψ n V ρ hρ l k B hk hB
  obtain ⟨hh, hp, hz⟩ := h4b F μ ψ hψ n V ρ hρ l k B B' hk hW hB hC
  exact ⟨B', hC, hh, hp, hz, h4c F μ ψ hψ n V ρ hρ l k B B' hk hB hC,
    h4d F μ ψ hψ n V ρ hρ l k B B' hk hB hC⟩

theorem inv_down [MeasurableSpace F] [BorelSpace F] (h4a : StableAverageExists) (h4b : FormHermitianPositive) (h4c : FormQuasiInvariantMirabolic) (h4d : FormEquivariantColumn)
    (μ : Measure F) [μ.IsAddHaarMeasure] {ψ : AddChar F ℂ} (hψ : PsiOK ψ) {n : ℕ} (hn : 1 < n)
    {ρ : Representation ℂ (GL (Fin n) F) V} (hρ : Smooth ρ) {l : V →ₗ[ℂ] ℂ} (hW : Whit ρ ψ l)
    {B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ} (hU : Unit' ρ B) (d : ℕ) (hd : d ≤ n - 2) :
    ∃ B₁, Inv ρ ψ l (n - 1 - d) B₁ := by
  induction d with
  | zero => exact ⟨B, inv_top hn hU⟩
  | succ d ih =>
    obtain ⟨B₁, h₁⟩ := ih (by omega)
    have e : n - 1 - d = n - 1 - (d + 1) + 1 := by omega
    rw [e] at h₁
    obtain ⟨B₂, -, h₂⟩ := inv_step h4a h4b h4c h4d μ hψ hρ hW (by omega) h₁
    exact ⟨B₂, h₂⟩

theorem final_form_bessel_bound : StableAverageExists → FormHermitianPositive → FormQuasiInvariantMirabolic → FormEquivariantColumn → L5 → L6 := by
  intro h4a h4b h4c h4d h5 F _ _ _ _ _ _ μ _ ψ hψ n V _ _ ρ hρ l B hn hW hU
  obtain ⟨B₁, h₁⟩ := inv_down h4a h4b h4c h4d μ hψ hn hρ hW hU (n - 2) le_rfl
  have e : n - 1 - (n - 2) = 0 + 1 := by omega
  rw [e] at h₁
  obtain ⟨B', hC, h'⟩ := inv_step h4a h4b h4c h4d μ hψ hρ hW (k := 0) (by omega) h₁
  exact ⟨B', h', h5 F μ ψ hψ n V ρ hρ l B₁ B' hn h₁ hC⟩

end GlobalTheory.CompanionTheory.SatakeBound

end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetShalikaBoundOfSteps

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.LFun PositivityTheory.JacquetShalikaLocal

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.SatakeBound

theorem jacquetShalikaBound_of_steps : ParameterUpperBound → liftZP_unit → ParameterAbsoluteValues → lift_levelP_alt₂ → G1 → G2 → G3 → G4 → GlobalTheory.Published.JacquetShalikaBound := by
  intro h10 h11 h11b h12 g1 g2 g3 g4 E _ _ _ a π hU w B hB α hα
  obtain ⟨L, rfl⟩ : ∃ L : List ℂˣ, (L : Multiset ℂˣ) = B := ⟨B.toList, Multiset.coe_toList B⟩
  have hcard : L.length = a := by simpa using hB.card
  subst hcard
  have hBz : (L : Multiset ℂˣ) = Finset.univ.val.map L.get := by rw [Fin.univ_val_map, List.ofFn_get]
  obtain ⟨i, rfl⟩ : ∃ i, L.get i = α := List.mem_iff_get.1 (Multiset.mem_coe.1 hα)
  have ha : 1 ≤ L.length := Fin.pos i
  induction π using Quotient.inductionOn with | _ π => ?_
  set z := L.get with hz
  let F := w.adicCompletion E
  letI : MeasurableSpace F := borel F
  haveI : BorelSpace F := ⟨rfl⟩
  have hB' : HasSatGL w (π.locRep w) (Finset.univ.val.map z) := by rw [← hBz]; exact hB
  obtain ⟨ψ, hψ, l, hl0, hW⟩ := g4 E L.length ha π w
  obtain ⟨v, g, hv, hlv⟩ := g2 E L.length π w _ hB' l hl0
  obtain ⟨Bf, hBf⟩ := g1 E L.length π hU w
  have hs := g3 E L.length π w
  obtain ⟨hq, h12'⟩ := h12 E w
  have hH : Heig (π.locRep w) v z := h12' L.length π.V (π.locRep w) v z hv
  have hq1 : (1 : ℝ) < (Ideal.absNorm w.asIdeal : ℝ) := by exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm w
  have hpair := h11b L.length z (h11 F L.length π.V (π.locRep w) Bf hBf v z hv.1 hH)
  have hup : ∀ j, ‖(z j : ℂ)‖ < Real.sqrt (Ideal.absNorm w.asIdeal : ℝ) := by
    intro j
    rcases Nat.lt_or_ge 1 L.length with h2 | h1
    · have := h10 F Measure.addHaar ψ hψ L.length π.V (π.locRep w) hs h2 l Bf hW hBf v z hH ⟨g, hlv⟩ j
      rwa [hq] at this
    · obtain ⟨k, hk⟩ := hpair j
      have hkj : k = j := Fin.ext (by have := k.2; have := j.2; omega)
      subst hkj
      have h0 : ‖(z k : ℂ)‖ = 1 := by
        have h00 : 0 ≤ ‖(z k : ℂ)‖ := norm_nonneg _
        nlinarith
      rw [h0, Real.lt_sqrt zero_le_one]
      simpa using hq1
  obtain ⟨k, hk⟩ := hpair i
  have hkpos : 0 < ‖(z k : ℂ)‖ := norm_pos_iff.2 (Units.ne_zero _)
  have hi : ‖(z i : ℂ)‖ = ‖(z k : ℂ)‖⁻¹ := eq_inv_of_mul_eq_one_right hk
  have hsq : (Ideal.absNorm w.asIdeal : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt (Ideal.absNorm w.asIdeal : ℝ) :=
    (Real.sqrt_eq_rpow _).symm
  refine ⟨?_, ?_⟩
  · rw [Real.rpow_neg (by positivity), hsq, hi]
    exact inv_strictAnti₀ hkpos (hup k)
  · rw [hsq]; exact hup i

end GlobalTheory.CompanionTheory.SatakeBound

end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemCongruenceSubgroupOfDiv

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GroundTheory.Automorphic GroundTheory.Automorphic.GLnLocal
  PositivityTheory.JacquetShalikaLocal
open scoped ValuativeRel Topology MatrixGroups

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.JSSmooth

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

theorem mem_congruenceSubgroup_of_div {c : ℕ} {g : GL (Fin n) F}
    (hg : Div (c + 1) ((g : Matrix (Fin n) (Fin n) F) - 1)) :
    g ∈ congruenceSubgroup F n (c + 1) := by
  choose y hy hgy using hg
  have hone : ∀ i j, (1 : Matrix (Fin n) (Fin n) F) i j ∈ 𝒪[F] := by
    intro i j
    rw [Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  have hent : ∀ i j, g i j - (1 : Matrix (Fin n) (Fin n) F) i j =
      (uniformizer F : F) ^ (c + 1) * y i j := fun i j => by
    rw [← hgy i j, Matrix.sub_apply]
  have hint : ∀ i j, g i j ∈ 𝒪[F] := fun i j => by
    have h1 : g i j = (uniformizer F : F) ^ (c + 1) * y i j +
        (1 : Matrix (Fin n) (Fin n) F) i j := by rw [← hent i j, sub_add_cancel]
    rw [h1]
    exact add_mem (mul_mem (pow_mem (uniformizer F).2 _) (hy i j)) (hone i j)
  let A : Matrix (Fin n) (Fin n) 𝒪[F] := Matrix.of fun i j => ⟨g i j, hint i j⟩
  have hres : (IsLocalRing.residue 𝒪[F]).mapMatrix A = 1 := by
    ext i j
    have hmem : A i j - (1 : Matrix (Fin n) (Fin n) 𝒪[F]) i j ∈ IsLocalRing.maximalIdeal 𝒪[F] := by
      have h1 : A i j - (1 : Matrix (Fin n) (Fin n) 𝒪[F]) i j =
          uniformizer F * (uniformizer F ^ c * ⟨y i j, hy i j⟩) := by
        apply Subtype.ext
        have h2 : (((1 : Matrix (Fin n) (Fin n) 𝒪[F]) i j : 𝒪[F]) : F) =
            (1 : Matrix (Fin n) (Fin n) F) i j := by
          rw [Matrix.one_apply, Matrix.one_apply]
          split_ifs <;> simp
        simp only [AddSubgroupClass.coe_sub, h2, MulMemClass.coe_mul, SubmonoidClass.coe_pow]
        change g i j - _ = _
        rw [hent i j]
        ring
      rw [h1]
      exact Ideal.mul_mem_right _ _ ((IsLocalRing.mem_maximalIdeal _).2 (irreducible_uniformizer F).not_isUnit)
    have h3 := (IsLocalRing.residue_eq_zero_iff _).2 hmem
    rw [map_sub, sub_eq_zero] at h3
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, h3, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have hdet : IsUnit A.det := by
    have h1 : IsLocalRing.residue 𝒪[F] A.det = 1 := by
      rw [RingHom.map_det, hres, Matrix.det_one]
    by_contra h
    have h2 := (IsLocalRing.residue_eq_zero_iff _).2 ((IsLocalRing.mem_maximalIdeal _).2 h)
    rw [h2] at h1
    exact zero_ne_one h1
  rw [mem_congruenceSubgroup_iff]
  refine ⟨⟨Matrix.GeneralLinearGroup.mk'' A hdet, Units.ext rfl⟩, fun i j => ?_⟩
  rw [hent i j, map_mul, map_pow]
  exact mul_le_of_le_one_right' ((Valuation.mem_integer_iff _ _).1 (hy i j))

theorem smooth_of_isSmooth {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL (Fin n) F) V) (h : GlobalTheory.PRep.IsSmooth ρ) : Smooth ρ := fun u => by
  have h1 : {g : GL (Fin n) F | ρ g u = u} ∈ 𝓝 (1 : GL (Fin n) F) :=
    (h u).mem_nhds (by simp)
  obtain ⟨m, -, hm⟩ := (hasBasis_nhds_one F n).mem_iff.1 h1
  exact ⟨m, fun g hg => hm (congruenceSubgroup_antitone F n (Nat.le_succ m)
    (mem_congruenceSubgroup_of_div hg))⟩

theorem g3 : G3 := fun _ _ _ _ _ π w => smooth_of_isSmooth _ (π.isSmooth_locRep w)

end GlobalTheory.CompanionTheory.JSSmooth

end
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaBound.JacquetShalikaBound

section

@[expose] public section

namespace PositivityTheory.JacquetShalikaLocal

theorem l0 : L0 := (@GlobalTheory.CompanionTheory.JSBound.l0 : L0)

theorem l1 : L1 := (@GlobalTheory.CompanionTheory.SatakeBound.orthogonality_of_lattice_character : L0 → L1) l0

theorem l2 : L2 := (@GlobalTheory.CompanionTheory.SatakeBound.LargeLattice.stability : L0 → L1 → L2) l0 l1

theorem l3 : L3 := (@GlobalTheory.CompanionTheory.SatakeBound.twisted_column_average_exists : L0 → L3) l0

theorem l3c : ColumnsMirabolic := (@GlobalTheory.CompanionTheory.JSBound.column_mirabolic_holds : ColumnsMirabolic)

theorem l3d : ColumnsUnipotent := (@GlobalTheory.CompanionTheory.JSBound.ColumnUnipotent.main : ColumnsUnipotent)

theorem l4s : FormCoefficientStability := (@GlobalTheory.CompanionTheory.JSBound.stability_coefficients : L0 → L2 → ColumnsMirabolic → FormCoefficientStability) l0 l2 l3c

theorem l4a : StableAverageExists := (@GlobalTheory.CompanionTheory.SatakeStable.stable_average : L0 → FormCoefficientStability → StableAverageExists) l0 l4s

theorem l4b : FormHermitianPositive := (@GlobalTheory.CompanionTheory.JSBoundStep.column_average_hermitian_positive : L0 → L3 → ColumnsMirabolic → FormHermitianPositive) l0 l3 l3c

theorem l4c : FormQuasiInvariantMirabolic := (@GlobalTheory.CompanionTheory.JSBound.column_average_quasi_invariant : L0 → ColumnsMirabolic → FormCoefficientStability → FormQuasiInvariantMirabolic) l0 l3c l4s

theorem l4d : FormEquivariantColumn := (@GlobalTheory.CompanionTheory.SatakeBound.equivariant_of_steps : L0 → ColumnsMirabolic → ColumnsUnipotent → FormCoefficientStability → FormEquivariantColumn) l0 l3c l3d l4s

theorem l5 : L5 := (@GlobalTheory.CompanionTheory.SatakeBessel.bessel_step : L0 → L1 → L2 → L3 → ColumnsMirabolic → L5) l0 l1 l2 l3 l3c

theorem l6 : L6 := (@GlobalTheory.CompanionTheory.SatakeBound.final_form_bessel_bound : StableAverageExists → FormHermitianPositive → FormQuasiInvariantMirabolic → FormEquivariantColumn → L5 → L6) l4a l4b l4c l4d l5

theorem l7 : L7 := (@GlobalTheory.CompanionTheory.SatakeBound.heckeEigenvector_whittaker : L7)

theorem l8 : L8 := (@GlobalTheory.CompanionTheory.SatakeBound.schur_row_recursion : L8)

theorem l9 : liftZP_newton := (@GlobalTheory.CompanionTheory.SatakeBound.norm_lt_one : liftZP_newton)

theorem l10 : ParameterUpperBound := (@GlobalTheory.CompanionTheory.Satake.l10 : L6 → L7 → L8 → liftZP_newton → ParameterUpperBound) l6 l7 l8 l9

theorem l11 : liftZP_unit := (@GlobalTheory.CompanionTheory.SatakeStable.l11 : liftZP_unit)

theorem l11b : ParameterAbsoluteValues := (@GlobalTheory.CompanionTheory.JSBound.symmetric_function_absolute_values : ParameterAbsoluteValues)

theorem l12 : lift_levelP_alt₂ := (@GlobalTheory.CompanionTheory.SatakeTyping.l12 : lift_levelP_alt₂)

theorem g1 : G1 := (@GlobalTheory.CompanionTheory.JSUnit.exists_unit_form : G1)

theorem g2 : G2 := (@GlobalTheory.CompanionTheory.SatakeBound.exists_translate_ne_zero : G2)

theorem g3 : G3 := (@GlobalTheory.CompanionTheory.JSSmooth.g3 : G3)

theorem g4 : G4 := (@GlobalTheory.CompanionTheory.JSBound.global_character_holds : G4)

theorem jacquetShalikaBound : GlobalTheory.Published.JacquetShalikaBound := (@GlobalTheory.CompanionTheory.SatakeBound.jacquetShalikaBound_of_steps : ParameterUpperBound → liftZP_unit → ParameterAbsoluteValues → lift_levelP_alt₂ → G1 → G2 → G3 → G4 → GlobalTheory.Published.JacquetShalikaBound) l10 l11 l11b l12 g1 g2 g3 g4

theorem jacquetShalika_of (h : GlobalTheory.Published.JacquetShalikaRigidity) : GlobalTheory.Published.JacquetShalika := ⟨h, jacquetShalikaBound⟩

end PositivityTheory.JacquetShalikaLocal
end
end
