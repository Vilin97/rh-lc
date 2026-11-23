module

public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.MemFormsOnOfMemSpan
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicConstantTermParabolic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CTSubmatrixMul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffConstantTermCocompactSmoothParameterFamiStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousIteratedRealLineDerivUnitaryAdelicStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealOneParamProductChartAdelicUnitaryStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviDecompositionGradedIsotropicFlagStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealLineContinuous
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StdParEqFlag
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModerateGrowthOfHasCompactSupport
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RderMemAutFormsCuspForms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CmDataIsCMExtAndGramIsHermND
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousIteratedFDerivRealOneParamProductLevel

section

@[expose] public section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut
open scoped TensorProduct ContDiff Topology

noncomputable section

namespace GlobalTheory.UAut.JointDer

theorem prod_ofFn_append {G : Type} [Monoid G] {d k : ℕ} (δ : Fin d → ℝ → G) (γ : Fin k → ℝ → G) (s : Fin d → ℝ)
    (t : Fin k → ℝ) :
    (List.ofFn fun i => Fin.append δ γ i (Fin.append s t i)).prod =
      (List.ofFn fun a => δ a (s a)).prod * (List.ofFn fun i => γ i (t i)).prod := by
  have e : (fun i => Fin.append δ γ i (Fin.append s t i)) = Fin.append (fun a => δ a (s a)) (fun i => γ i (t i)) := by
    funext i
    refine Fin.addCases (fun a => ?_) (fun j => ?_) i <;> simp [Fin.append_left, Fin.append_right]
  rw [e, List.ofFn_fin_append, List.prod_append]

theorem contDiff_append {d k : ℕ} : ContDiff ℝ ∞ fun q : (Fin d → ℝ) × (Fin k → ℝ) => Fin.append q.1 q.2 := by
  refine contDiff_pi.2 fun i => ?_
  refine Fin.addCases (fun a => ?_) (fun j => ?_) i
  · simp only [Fin.append_left]; exact (contDiff_apply ℝ (fun _ => ℝ) a).comp contDiff_fst
  · simp only [Fin.append_right]; exact (contDiff_apply ℝ (fun _ => ℝ) j).comp contDiff_snd

theorem iteratedFDeriv_slice {A B : Type} [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B]
    [NormedSpace ℝ B] {H : A × B → ℂ} (hH : ContDiff ℝ ∞ H) (m : ℕ) (a : A) (t : B) :
    iteratedFDeriv ℝ m (fun t => H (a, t)) t =
      (iteratedFDeriv ℝ m H (a, t)).compContinuousLinearMap fun _ => ContinuousLinearMap.inr ℝ A B := by
  have e : (fun t => H (a, t)) = (fun q => H ((a, 0) + q)) ∘ ContinuousLinearMap.inr ℝ A B := by
    funext t; simp
  rw [e, ContinuousLinearMap.iteratedFDeriv_comp_right _
    (show ContDiff ℝ ∞ fun q => H ((a, 0) + q) from hH.comp (contDiff_const.add contDiff_id)) _
    (by exact_mod_cast le_top), iteratedFDeriv_comp_add_left]
  simp

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {J : Matrix (Fin n) (Fin n) E}

theorem commute_prod_realLine {k : ℕ} {γ : Fin k → ℝ → GAd σ J} (hγ : ∀ i, IsRealLine σ J (γ i)) (t : Fin k → ℝ)
    {u : GAd σ J} (hu : u ∈ finPts σ J) : Commute (List.ofFn fun i => γ i (t i)).prod u := by
  refine Commute.list_prod_left _ _ fun x hx => ?_
  obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hx
  obtain ⟨w, τ, Z, -, h⟩ := hγ i
  obtain ⟨y, e, -⟩ := h (t i)
  show Commute (γ i (t i)) u
  rw [e]
  exact commute_embArch σ J y (mem_finPts_iff_forall.1 hu w)

end GlobalTheory.UAut.JointDer


open GlobalTheory.UAut.JointDer in
theorem GlobalTheory.UAut.continuous_iteratedFDeriv_prod_realLine : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (d : ℕ) (δ : Fin d → ℝ → GAd σ J), (∀ a, IsRealLine σ J (δ a)) → (∀ U ∈ 𝓝 (1 : GAd σ J), ∃ W ∈ 𝓝 (1 : GAd σ J), ∃ s : GAd σ J → (Fin d → ℝ), ContinuousAt s 1 ∧ ∀ y ∈ W, ∃ u ∈ U, u ∈ finPts σ J ∧ y = (List.ofFn fun a => δ a (s y a)).prod * u) → ∀ φ : GAd σ J → ℂ, (∃ U : Subgroup (GAd σ J), IsOpen (U : Set (GAd σ J)) ∧ ∀ k ∈ U, k ∈ finPts σ J → ∀ g, φ (g * k) = φ g) → IsSm σ J φ → ∀ (k : ℕ) (γ : Fin k → ℝ → GAd σ J), (∀ i, IsRealLine σ J (γ i)) → ∀ m : ℕ, Continuous fun p : GAd σ J × (Fin k → ℝ) => iteratedFDeriv ℝ m (fun t : Fin k → ℝ => φ (p.1 * (List.ofFn fun i => γ i (t i)).prod)) p.2 := by
  intro F E _ _ _ _ _ σ _ n J _ d δ hδ hchart φ hlev hsm k γ hγ m
  obtain ⟨U, hUo, hU⟩ := hlev
  obtain ⟨W, hW, s, hs, hWs⟩ := hchart _ (hUo.mem_nhds U.one_mem)
  set P : (Fin k → ℝ) → GAd σ J := fun t => (List.ofFn fun i => γ i (t i)).prod with hP
  set Q : (Fin d → ℝ) → GAd σ J := fun s => (List.ofFn fun a => δ a (s a)).prod with hQ
  refine continuous_iff_continuousAt.2 fun p₀ => ?_
  obtain ⟨x₀, t₀⟩ := p₀
  let H : (Fin d → ℝ) × (Fin k → ℝ) → ℂ := fun q => φ (x₀ * (Q q.1 * P q.2))
  have hH : ContDiff ℝ ∞ H := by
    have h1 := hsm (d + k) (Fin.append δ γ)
      (fun i => Fin.addCases (fun a => by simpa [Fin.append_left] using hδ a)
        (fun j => by simpa [Fin.append_right] using hγ j) i) x₀
    have h2 := h1.comp contDiff_append
    convert h2 using 1
    funext q
    simp [H, hP, hQ, prod_ofFn_append]
  have key : ∀ x, x₀⁻¹ * x ∈ W → ∀ t, φ (x * P t) = H (s (x₀⁻¹ * x), t) := by
    intro x hx t
    obtain ⟨u, huU, huf, e⟩ := hWs _ hx
    have hc : Commute (P t) u := commute_prod_realLine hγ t huf
    have hx' : x = x₀ * (Q (s (x₀⁻¹ * x)) * u) := by
      simp only [hQ]
      rw [← e]
      group
    calc φ (x * P t) = φ (x₀ * (Q (s (x₀⁻¹ * x)) * u) * P t) := by rw [← hx']
      _ = φ ((x₀ * (Q (s (x₀⁻¹ * x)) * P t)) * u) := by
          congr 1
          simp only [mul_assoc]
          rw [hc.eq]
      _ = H (s (x₀⁻¹ * x), t) := hU u huU huf _
  have hev : ∀ᶠ p : GAd σ J × (Fin k → ℝ) in 𝓝 (x₀, t₀),
      (iteratedFDeriv ℝ m H (s (x₀⁻¹ * p.1), p.2)).compContinuousLinearMap
        (fun _ => ContinuousLinearMap.inr ℝ (Fin d → ℝ) (Fin k → ℝ)) =
      iteratedFDeriv ℝ m (fun t => φ (p.1 * P t)) p.2 := by
    have hmem : {p : GAd σ J × (Fin k → ℝ) | x₀⁻¹ * p.1 ∈ W} ∈ 𝓝 (x₀, t₀) :=
      (continuous_const.mul continuous_fst).continuousAt.preimage_mem_nhds (by simpa using hW)
    filter_upwards [hmem] with p hp
    rw [← iteratedFDeriv_slice hH, show (fun t => φ (p.1 * P t)) = fun t => H (s (x₀⁻¹ * p.1), t) from
      funext (key p.1 hp)]
  refine ContinuousAt.congr ?_ hev
  have hcont : Continuous fun q => (iteratedFDeriv ℝ m H q).compContinuousLinearMap
      (fun _ => ContinuousLinearMap.inr ℝ (Fin d → ℝ) (Fin k → ℝ)) :=
    (ContinuousMultilinearMap.continuous_precomp _).comp (hH.continuous_iteratedFDeriv (by exact_mod_cast le_top))
  have hsx : ContinuousAt (fun p : GAd σ J × (Fin k → ℝ) => s (x₀⁻¹ * p.1)) (x₀, t₀) :=
    hs.comp_of_eq (continuous_const.mul continuous_fst).continuousAt (by simp)
  exact hcont.continuousAt.comp (hsx.prodMk continuousAt_snd)

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousIteratedFDerivRealOneParamProductLevelStatement

section

@[expose] public section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut
open scoped TensorProduct ContDiff Topology

theorem _root_.GlobalTheory.T.continuous_iteratedFDeriv_realOneParamProduct_levelFunction : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (d : ℕ) (δ : Fin d → ℝ → GAd σ J), (∀ a, IsRealLine σ J (δ a)) → (∀ U ∈ 𝓝 (1 : GAd σ J), ∃ W ∈ 𝓝 (1 : GAd σ J), ∃ s : GAd σ J → (Fin d → ℝ), ContinuousAt s 1 ∧ ∀ y ∈ W, ∃ u ∈ U, u ∈ finPts σ J ∧ y = (List.ofFn fun a => δ a (s y a)).prod * u) → ∀ φ : GAd σ J → ℂ, (∃ U : Subgroup (GAd σ J), IsOpen (U : Set (GAd σ J)) ∧ ∀ k ∈ U, k ∈ finPts σ J → ∀ g, φ (g * k) = φ g) → IsSm σ J φ → ∀ (k : ℕ) (γ : Fin k → ℝ → GAd σ J), (∀ i, IsRealLine σ J (γ i)) → ∀ m : ℕ, Continuous fun p : GAd σ J × (Fin k → ℝ) => iteratedFDeriv ℝ m (fun t : Fin k → ℝ => φ (p.1 * (List.ofFn fun i => γ i (t i)).prod)) p.2 := by
  first | exact @GlobalTheory.UAut.continuous_iteratedFDeriv_prod_realLine | exact GlobalTheory.UAut.continuous_iteratedFDeriv_prod_realLine | (intros; apply GlobalTheory.UAut.continuous_iteratedFDeriv_prod_realLine <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GlobalProofs.ConstantTermModerateGrowthInherited

section

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.ConstMod

section General

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut
open GlobalTheory.AutomorphicL2Unitary (LeftInv)
open GlobalTheory.Cusp (Cocompact constTermOn)
open GlobalTheory.UAut.ConstAut
open GlobalTheory.ThK.SmoothLev (IsSmModOn)
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem isSmModOn_constTermOn (h : IsCMExt F E σ) (hJ : IsHermND σ J) {r : ℕ} {C : Matrix (Fin n) (Fin r) E}
    (d : Fin r → ℕ) (hC : IsIsoCols σ J C) {Γ : Set (GAd σ J)} {φ c : GAd σ J → ℂ}
    (hΓ : ((ratPts σ J ⊓ parFlag σ J C d : Subgroup (GAd σ J)) : Set (GAd σ J)) ⊆ Γ)
    (hφ : IsSmModOn σ J Γ φ) (hc : IsConstTermOn σ J (unipFlag σ J C d) φ c) :
    IsSmModOn σ J (leftGrp σ J C d : Set (GAd σ J)) c ∧ ∀ l : List (ℝ → GAd σ J), (∀ γ ∈ l, IsRealLine σ J γ) →
      IsConstTermOn σ J (unipFlag σ J C d) (l.foldr lineDer φ) (l.foldr lineDer c) := by
  classical
  haveI := locallyCompact_unipFlag hJ (sigma_sigma h) hC d
  have hs : IsSm σ J φ := hφ.smooth
  have hφΓ : LeftInv (ratPts σ J ⊓ parFlag σ J C d) φ := fun γ hγ => hφ.left γ (hΓ hγ)
  obtain ⟨hco, e⟩ := hc.eq_constTermOn_par h hJ hC hφΓ
  have hcont : ∀ l : List (ℝ → GAd σ J), (∀ γ ∈ l, IsRealLine σ J γ) → Continuous (l.foldr lineDer φ) :=
    GlobalTheory.T.continuous_iteratedRealLineDeriv_unitaryAdelic F E σ h n J hJ φ hφ.level hφ.cont hs
  have hleft : ∀ l : List (ℝ → GAd σ J), LeftInv (ratPts σ J ⊓ parFlag σ J C d) (l.foldr lineDer φ) :=
    leftInv_foldr hφΓ
  have hder : ∀ l : List (ℝ → GAd σ J), (∀ γ ∈ l, IsRealLine σ J γ) →
      l.foldr lineDer c = constTermOn (ratPts σ J ⊓ parFlag σ J C d) (unipFlag σ J C d) (l.foldr lineDer φ) := by
    intro l
    induction l with
    | nil => intro _; exact e
    | cons γ l ih =>
      intro hl
      have hl' : ∀ γ' ∈ l, IsRealLine σ J γ' := fun γ' h' => hl γ' (List.mem_cons_of_mem _ h')
      have hγ : IsRealLine σ J γ := hl γ List.mem_cons_self
      funext x
      have hx := GlobalTheory.CuspLie.hasDerivAt_constTermOn hco (hleft l) (hcont l hl') (hleft (γ :: l)) (hcont (γ :: l) hl)
        (GlobalTheory.RealLineCont.continuous_of_isRealLine F E σ h n J γ hγ) (hasDerivAt_foldr h hs hl' hγ) x
      rw [realLine_zero h hγ, mul_one] at hx
      rw [List.foldr_cons, ih hl']
      exact hx.deriv
  have hct : ∀ l : List (ℝ → GAd σ J), (∀ γ ∈ l, IsRealLine σ J γ) →
      IsConstTermOn σ J (unipFlag σ J C d) (l.foldr lineDer φ) (l.foldr lineDer c) := by
    intro l hl
    obtain ⟨c', hc', -⟩ := existsUnique_isConstTermOn h hJ hC d (φ := l.foldr lineDer φ)
      fun γ hγ => hleft l γ ⟨hγ.1, unipFlag_le_parFlag hJ (sigma_sigma h) hC d hγ.2⟩
    rwa [hder l hl, ← (hc'.eq_constTermOn_par h hJ hC (hleft l)).2]
  have hlevel : ∃ U : Subgroup (GAd σ J), IsOpen (U : Set (GAd σ J)) ∧
      ∀ k ∈ U, k ∈ finPts σ J → ∀ g, c (g * k) = c g := by
    obtain ⟨U, hU, hUk⟩ := hφ.level
    refine ⟨U, hU, fun k hk hf g => ?_⟩
    rw [e, ← GlobalTheory.Cusp.constTermOn_mul_right]
    exact congrArg (fun f => constTermOn _ _ f g) (funext fun y => hUk k hk hf y)
  have hsm : IsSm σ J c := by
    obtain ⟨dd, δ, hδ, hW⟩ := GlobalTheory.T.exists_realOneParamProduct_chart_adelicUnitary F E σ h n J hJ
    intro k γ hγ g
    have := GlobalTheory.T.contDiff_constantTermCocompact_smoothParameterFamily hco (fun x t => φ (x * (List.ofFn fun i => γ i (t i)).prod))
      (fun γ' hγ' x t => by simp only [mul_assoc]; exact hφΓ γ' hγ' _) (fun x => hs k γ hγ x)
      (GlobalTheory.T.continuous_iteratedFDeriv_realOneParamProduct_levelFunction F E σ h n J hJ dd δ hδ hW φ hφ.level hs k γ hγ) g
    simpa [e, GlobalTheory.Cusp.constTermOn_mul_right] using this
  have hgrowth : ∃ M : ℕ, ∀ l : List (ℝ → GAd σ J), (∀ γ ∈ l, IsRealLine σ J γ) →
      ∃ B : ℝ, ∀ g, ‖l.foldr lineDer c g‖ ≤ B * (height σ J g : ℝ) ^ M := by
    obtain ⟨M, hM⟩ := hφ.growth
    obtain ⟨K0, hK0, hs'⟩ := id hco
    haveI := hco.isProbabilityMeasure
    obtain ⟨A, hA⟩ := (hK0.image continuous_subtype_val).exists_bound_of_continuousOn
      (f := fun x => (height σ J x : ℝ)) (NNReal.continuous_coe.comp (continuous_height_GAd σ J)).continuousOn
    refine ⟨M, fun l hl => ?_⟩
    obtain ⟨B, hB⟩ := hM l hl
    refine ⟨max B 0 * max A 0 ^ M, fun g => ?_⟩
    have h1 : ∀ x : unipFlag σ J C d, ‖l.foldr lineDer φ ((x : GAd σ J) * g)‖ ≤
        max B 0 * (max A 0 * (height σ J g : ℝ)) ^ M := by
      intro x
      obtain ⟨γ, hγ, hk⟩ := hs' x
      have e1 : l.foldr lineDer φ ((x : GAd σ J) * g) =
          l.foldr lineDer φ (((γ * x : unipFlag σ J C d) : GAd σ J) * g) := by
        rw [Subgroup.coe_mul, mul_assoc]; exact (hleft l _ hγ _).symm
      have e2 : (height σ J ((γ * x : unipFlag σ J C d) : GAd σ J) : ℝ) ≤ max A 0 := by
        have := hA _ ⟨_, hk, rfl⟩
        rw [Real.norm_eq_abs] at this
        exact (le_abs_self _).trans (this.trans (le_max_left _ _))
      have e3 : (height σ J (((γ * x : unipFlag σ J C d) : GAd σ J) * g) : ℝ) ≤ max A 0 * height σ J g :=
        calc (height σ J (((γ * x : unipFlag σ J C d) : GAd σ J) * g) : ℝ)
            ≤ height σ J ((γ * x : unipFlag σ J C d) : GAd σ J) * height σ J g := by
              exact_mod_cast height_mul_le σ J _ _
          _ ≤ max A 0 * height σ J g := mul_le_mul_of_nonneg_right e2 (NNReal.coe_nonneg _)
      rw [e1]
      calc _ ≤ B * (height σ J (((γ * x : unipFlag σ J C d) : GAd σ J) * g) : ℝ) ^ M := hB _
        _ ≤ max B 0 * (height σ J (((γ * x : unipFlag σ J C d) : GAd σ J) * g) : ℝ) ^ M :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (NNReal.coe_nonneg _) _)
        _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (NNReal.coe_nonneg _) e3 _) (le_max_right _ _)
    rw [hder l hl]
    refine (norm_integral_le_of_norm_le_const (μ := GlobalTheory.Cusp.probMeasure _ _) (.of_forall fun q => h1 q.out)).trans
      (le_of_eq ?_)
    simp [mul_pow, mul_assoc]
  exact ⟨⟨hc.leftInv h hJ hC hφΓ, hlevel, hc.continuous h hJ hC hφΓ hφ.cont, hsm, hgrowth⟩, hct⟩

theorem depth_lt {r t : ℕ} (ht : t ≤ r) {T : Finset (Fin r)} {i j : Fin t} {k : Fin r} (hk : k ∈ T)
    (h1 : j.val ≤ k.val) (h2 : k.val < i.val) :
    (T.filter (· < Fin.castLE ht j)).card < (T.filter (· < Fin.castLE ht i)).card := by
  refine Finset.card_lt_card ⟨fun x hx => ?_, fun hsub => ?_⟩
  · simp only [Finset.mem_filter, Fin.lt_def, Fin.val_castLE] at hx ⊢
    exact ⟨hx.1, by omega⟩
  · have h3 := hsub (Finset.mem_filter.2 ⟨hk, Fin.lt_def.2 (by simpa using h2)⟩)
    have h4 := Fin.lt_def.1 (Finset.mem_filter.1 h3).2
    simp only [Fin.val_castLE] at h4
    omega

theorem exists_block_of_subset {r s t : ℕ} (X : Matrix (Fin n) (Fin r) E) {S T : Finset (Fin r)} (hST : S ⊆ T)
    (hs : s ≤ r) (ht : t ≤ r) (hst : s ≤ t) (hS : ∀ i : Fin r, i.val < s ↔ ∃ k ∈ S, i ≤ k)
    {M : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)} {B : Matrix (Fin t) (Fin t) (AF F ⊗[F] E)}
    (hB : B.BlockTriangular fun i : Fin t => (T.filter (· < Fin.castLE ht i)).card)
    (e : M * adMat F (X.submatrix id (Fin.castLE ht)) = adMat F (X.submatrix id (Fin.castLE ht)) * B) :
    ∃ B' : Matrix (Fin s) (Fin s) (AF F ⊗[F] E),
      (B'.BlockTriangular fun i : Fin s => (S.filter (· < Fin.castLE hs i)).card) ∧
      M * adMat F (X.submatrix id (Fin.castLE hs)) = adMat F (X.submatrix id (Fin.castLE hs)) * B' := by
  refine ⟨B.submatrix (Fin.castLE hst) (Fin.castLE hst), fun i j hij => ?_, Matrix.ext fun x j => ?_⟩
  · obtain ⟨k, hk, hk'⟩ := Finset.exists_mem_notMem_of_card_lt_card hij
    have hk1 := Finset.mem_filter.1 hk
    have h2 : k.val < i.val := by simpa [Fin.lt_def] using hk1.2
    have h1 : j.val ≤ k.val := by
      by_contra hc
      exact hk' (Finset.mem_filter.2 ⟨hk1.1, Fin.lt_def.2 (by simpa using not_le.1 hc)⟩)
    exact hB (depth_lt ht (hST hk1.1) (i := Fin.castLE hst i) (j := Fin.castLE hst j) (by simpa using h1) (by simpa using h2))
  · have e1 := congrFun (congrFun e x) (Fin.castLE hst j)
    have l1 : (M * adMat F (X.submatrix id (Fin.castLE hs))) x j =
        (M * adMat F (X.submatrix id (Fin.castLE ht))) x (Fin.castLE hst j) := rfl
    rw [l1, e1, Matrix.mul_apply, Matrix.mul_apply]
    symm
    refine Fintype.sum_of_injective (Fin.castLE hst) (Fin.castLE_injective hst) _ _ (fun i hi => ?_) fun i => rfl
    have hi' : s ≤ i.val := by
      by_contra hc
      exact hi ⟨⟨i.val, not_le.1 hc⟩, rfl⟩
    obtain ⟨k, hk, hjk⟩ := (hS (Fin.castLE hs j)).1 (by simp)
    have hks : k.val < s := (hS k).2 ⟨k, hk, le_rfl⟩
    have hz : B i (Fin.castLE hst j) = 0 :=
      hB (depth_lt ht (hST hk) (by simpa [Fin.le_def] using hjk) (by omega))
    rw [hz, mul_zero]

theorem parFlag_le_of_subset {r s t : ℕ} (X : Matrix (Fin n) (Fin r) E) {S T : Finset (Fin r)} (hST : S ⊆ T)
    (hs : s ≤ r) (ht : t ≤ r) (hst : s ≤ t) (hS : ∀ i : Fin r, i.val < s ↔ ∃ k ∈ S, i ≤ k) :
    parFlag σ J (X.submatrix id (Fin.castLE ht)) (fun i : Fin t => (T.filter (· < Fin.castLE ht i)).card) ≤
      parFlag σ J (X.submatrix id (Fin.castLE hs)) (fun i : Fin s => (S.filter (· < Fin.castLE hs i)).card) :=
  fun _ ⟨⟨B, hB, e⟩, B', hB', e'⟩ =>
    ⟨exists_block_of_subset X hST hs ht hst hS hB e, exists_block_of_subset X hST hs ht hst hS hB' e'⟩

def top {r : ℕ} (S : Finset (Fin r)) : ℕ := S.sup fun k => k.val + 1

theorem top_le {r : ℕ} (S : Finset (Fin r)) : top S ≤ r := Finset.sup_le fun k _ => k.2

theorem top_mono {r : ℕ} {S T : Finset (Fin r)} (h : S ⊆ T) : top S ≤ top T := Finset.sup_mono h

theorem lt_top_iff {r : ℕ} (S : Finset (Fin r)) (i : Fin r) : i.val < top S ↔ ∃ k ∈ S, i ≤ k := by
  rw [top, Finset.lt_sup_iff]
  exact exists_congr fun k => and_congr_right fun _ => by rw [Fin.le_def]; omega

theorem leftGrp_eq (h : IsCMExt F E σ) (hJ : IsHermND σ J) {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}
    (hW : IsWittFrame σ J X Y) (S : Finset (Fin r)) :
    leftGrp σ J (X.submatrix id (Fin.castLE (top_le S)))
        (fun i : Fin (top S) => (S.filter (· < Fin.castLE (top_le S) i)).card) =
      GlobalTheory.StdPar.unip σ J X S ⊔ (ratPts σ J ⊓ GlobalTheory.StdPar.levi σ J X Y S) := by
  obtain ⟨hu, hl, -⟩ := GlobalTheory.TieStd.stdPar_eq_flag F E σ h n J hJ r X Y hW S (top S) (top_le S) (lt_top_iff S)
    (fun i : Fin (top S) => (S.filter (· < Fin.castLE (top_le S) i)).card) fun _ => rfl
  have hg := (GlobalTheory.T.leviDecomposition_gradedIsotropicFlag F E σ h n J hJ (top S) (X.submatrix id (Fin.castLE (top_le S)))
    (Y.submatrix id (Fin.castLE (top_le S))) (fun i : Fin (top S) => (S.filter (· < Fin.castLE (top_le S) i)).card)
    (by rw [GlobalTheory.TieStd.cT_submatrix_mul, hW.xx]; ext; simp)
    (by rw [GlobalTheory.TieStd.cT_submatrix_mul, hW.yy]; ext; simp)
    (by rw [GlobalTheory.TieStd.cT_submatrix_mul, hW.xy]; exact Matrix.submatrix_one _ (Fin.castLE_injective _))).2.2.1
  rw [hg, hu, hl]

end General

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin

theorem isSmModOn_constAlong : ∀ (D : D7) (V : HSp D) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ S T : Finset (Fin m), S ⊆ T → T.Nonempty → ∀ φ c : GA D V → ℂ, IsSmModOn D.sp.cm.sig V.gram (leftSub V X Y S : Set (GA D V)) φ → IsConstAlong D.sp.cm.sig V.gram X T φ c → IsSmModOn D.sp.cm.sig V.gram (leftSub V X Y T : Set (GA D V)) c ∧ ∀ l : List (ℝ → GA D V), (∀ γ ∈ l, GlobalTheory.SiegelSet.IsRealLine D.sp.cm.sig V.gram γ) → IsConstAlong D.sp.cm.sig V.gram X T (l.foldr GlobalTheory.SiegelSet.lineDer φ) (l.foldr GlobalTheory.SiegelSet.lineDer c) := by
  intro D V m X Y hW S T hST _ φ c hφ hc
  obtain ⟨h, hJ'⟩ := GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND D.host.F D.host.E D.sp.cm
  have hJ := hJ' V
  obtain ⟨hu, -, -⟩ := GlobalTheory.TieStd.stdPar_eq_flag _ _ D.sp.cm.sig h _ V.gram hJ m X Y hW T (top T) (top_le T) (lt_top_iff T)
    (fun i : Fin (top T) => (T.filter (· < Fin.castLE (top_le T) i)).card) fun _ => rfl
  have hC := GlobalTheory.UAut.isIsoCols_of_isWittFrame hW (GlobalTheory.SiegelSet.sigma_sigma h) hJ (top_le T)
  have hc' : GlobalTheory.UAut.IsConstTermOn D.sp.cm.sig V.gram (GlobalTheory.UAut.unipFlag D.sp.cm.sig V.gram (X.submatrix id (Fin.castLE (top_le T)))
      (fun i : Fin (top T) => (T.filter (· < Fin.castLE (top_le T) i)).card)) φ c := hu ▸ hc
  have hΓ : ((GlobalTheory.AdelicU.ratPts D.sp.cm.sig V.gram ⊓ GlobalTheory.UAut.parFlag D.sp.cm.sig V.gram (X.submatrix id (Fin.castLE (top_le T)))
      (fun i : Fin (top T) => (T.filter (· < Fin.castLE (top_le T) i)).card) : Subgroup (GA D V)) : Set (GA D V)) ⊆
      (leftSub V X Y S : Set (GA D V)) := by
    intro p hp
    have e := leftGrp_eq h hJ hW S
    have : p ∈ GlobalTheory.UAut.leftGrp D.sp.cm.sig V.gram (X.submatrix id (Fin.castLE (top_le S)))
        (fun i : Fin (top S) => (S.filter (· < Fin.castLE (top_le S) i)).card) :=
      Subgroup.mem_sup_right ⟨hp.1, parFlag_le_of_subset X hST (top_le S) (top_le T) (top_mono hST) (lt_top_iff S) hp.2⟩
    rw [e] at this
    exact this
  obtain ⟨r1, r2⟩ := isSmModOn_constTermOn h hJ _ hC hΓ hφ hc'
  refine ⟨?_, fun l hl => ?_⟩
  · have e : (leftSub V X Y T : Subgroup (GA D V)) = GlobalTheory.UAut.leftGrp D.sp.cm.sig V.gram (X.submatrix id (Fin.castLE (top_le T)))
        (fun i : Fin (top T) => (T.filter (· < Fin.castLE (top_le T) i)).card) := (leftGrp_eq h hJ hW T).symm
    rw [e]
    exact r1
  · have := r2 l hl
    rw [← hu] at this
    exact this

end GlobalTheory.CompanionTheory.Hypotheses₂.ConstMod

end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GlobalProofs.ConstantTermModerateGrowthInheritedStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin

theorem _root_.GlobalTheory.T.constant_term_moderate_growth_inherited : ∀ (D : D7) (V : HSp D) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ S T : Finset (Fin m), S ⊆ T → T.Nonempty → ∀ φ c : GA D V → ℂ, IsSmModOn D.sp.cm.sig V.gram (leftSub V X Y S : Set (GA D V)) φ → IsConstAlong D.sp.cm.sig V.gram X T φ c → IsSmModOn D.sp.cm.sig V.gram (leftSub V X Y T : Set (GA D V)) c ∧ ∀ l : List (ℝ → GA D V), (∀ γ ∈ l, GlobalTheory.SiegelSet.IsRealLine D.sp.cm.sig V.gram γ) → IsConstAlong D.sp.cm.sig V.gram X T (l.foldr GlobalTheory.SiegelSet.lineDer φ) (l.foldr GlobalTheory.SiegelSet.lineDer c) := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.ConstMod.isSmModOn_constAlong | exact GlobalTheory.CompanionTheory.Hypotheses₂.ConstMod.isSmModOn_constAlong | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.ConstMod.isSmModOn_constAlong <;> assumption)
end
end
