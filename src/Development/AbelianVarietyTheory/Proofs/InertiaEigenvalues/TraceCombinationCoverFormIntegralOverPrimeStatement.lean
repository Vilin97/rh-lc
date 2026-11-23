module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IntFormsSubset
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormIntegralLatticeUnramifiedDescent
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsFiniteExtensionIntegralFramedPointLiftCoveStatement
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IntegralFramedPointBaseChangeStable
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
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CompIntField
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.DisjointSplitLevelPlaces
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoverSectionsLinearIndependentAdelicReadings
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPullbackSectionToLevelCover
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TraceIntegralOfSmallAtOtherPlacesStatement
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BaseSectionsValuesIntegralAtCoverLift

section

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.NX Formalism.IndefR.FWT Formalism.IndefR.Lev GlobalTheory.CoverRead GlobalTheory.TowerCov GlobalTheory.Member
open scoped TensorProduct Matrix
open Classical
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CoverLiftVal

theorem valV_le_one_of_nval {V K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K']
    [Algebra V K'] [IsFractionRing V K'] {e : ℕ} (he : 0 < e) {x : K'} (h : 0 ≤ nval V e x) : valV V x ≤ 1 := by
  by_cases hx : x = 0
  · subst hx; simp
  rw [nval_of_ne hx, EReal.coe_nonneg] at h
  have he' : (0 : ℝ) < e := by exact_mod_cast he
  have h1 : (0 : ℝ) ≤ (vV V x : ℝ) := by
    have := mul_nonneg h he'.le
    rwa [div_mul_cancel₀ _ he'.ne'] at this
  have h2 : 0 ≤ vV V x := by exact_mod_cast h1
  unfold vV at h2
  rw [← WithZero.log_le_log (valV_ne_zero hx) one_ne_zero, WithZero.log_one]
  omega

theorem le_one_at_lift : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, ∀ C : Cover T j σ, C.IsUnif → ∀ (la : HeightOneSpectrum (𝓞 C.d.c₂.F)) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (m : ℕ) (β : Fin m → Rul (T.Q.Xo j) T.Q.c) (g : Fin m → Rul C.d.Xo₂ C.d.c₂), (∀ k, β k ∈ sec (T.Q.Xo j) T.Q.c a n) → (∀ k, g k ∈ sec C.d.Xo₂ C.d.c₂ a n) → (∀ k, C.IsPull (β k) (g k)) → ∀ y : Fin m → C.d.c₂.F, (∀ v ∈ valSet C.d.Xo₂ C.d.c₂ (algCls C.d.Xo₂ C.d.c₂) la, 0 ≤ v (∑ k, y k • g k)) → ∀ (T0 : CDVR) (io : T.Q.c.F →+* T0.Fr) (pt : IntFr (T.Q.Xo j) T.Q.c T0 io), T0.FinRes → ∀ (T' : CDVR) (i : T0.Fr →+* T'.Fr) (e' : ℕ) (τ : C.d.c₂.F →+* T'.Fr) (e'' : ℕ), 0 < e' → (∀ z : T0.Fr, z ≠ 0 → vV T'.V (i z) = (e' : ℤ) * vV T0.V z) → T'.FinRes → (∀ z : T.Q.c.F, τ (C.inc z) = i (io z)) → OverLa la T'.V τ e'' → valV T'.V (∑ k, τ (y k) * i (evI pt (β k))) ≤ 1 := by
  intro D T hL j hj σ C hU la a n m β g hβ hg hpull y hint T0 io pt hT0 T' i e' τ e'' he' hi hT' hτ ho
  obtain ⟨y₁, φ, hφ, hmap⟩ := GlobalTheory.IntFrBaseChange.exists_intFr_baseChange _ _ _ _ (T.Q.Xo j) T.Q.c T0 T' io pt i e' he' hi
  let σ' : C.c'.F →+* T'.Fr := τ.comp (C.d.eF : C.c'.F →+* C.d.c₂.F)
  have hσ' : ∀ z, σ' (incF T.Q.c C.c' C.hle z) = (i.comp io) z := fun z => hτ z
  obtain ⟨y₂, hy₂⟩ := GlobalTheory.SupDescent.exists_intFr_ext C.hle (io := i.comp io) σ' hσ' y₁
  obtain ⟨T'', iT, e₃, y₃, io₂, y₄, hext, hT'', hio₂, hover⟩ := GlobalTheory.T.exists_finiteExtension_integralFramedPoint_lift_cover _ _ _ _ (T.Q.Xo j) C.c' 0 C.d hU.1 T' σ' y₂ hT'
  obtain ⟨he₃, hv₃, ψ, hψe, hψ⟩ := hext
  have hio : io₂ = iT.comp τ := by
    ext z
    obtain ⟨w, rfl⟩ := C.d.eF.surjective z
    exact hio₂ w
  subst hio
  letI : Algebra C.c'.F T''.Fr := (iT.comp σ').toAlgebra
  letI : Algebra C.d.c₂.F T''.Fr := (iT.comp τ).toAlgebra
  letI : Algebra T.Q.c.F T''.Fr := (iT.comp (i.comp io)).toAlgebra
  letI : Algebra T.Q.c.F T'.Fr := (i.comp io).toAlgebra
  letI : Algebra C.c'.F T'.Fr := σ'.toAlgebra
  have hA : AlgOver T.Q.c C.c' C.hle T''.Fr := fun z => congrArg iT (hσ' z)
  let φ₂ : T'.Fr →ₐ[T.Q.c.F] T''.Fr := { iT with commutes' := fun _ => rfl }
  have hmap₂ : FrMap φ₂ (y₂.1.res C.hle hσ') (y₃.1.res C.hle hA) := by
    obtain ⟨hx, hu, pm, h1, h2, h3⟩ := hψ
    rw [hψe] at hx hu h2
    exact ⟨hx, hu, pm, h1, h2, h3⟩
  have hval : ∀ k, evI y₄ (g k) = iT (i (evI pt (β k))) := fun k => by
    have h1 := hpull k T''.Fr hA (fun _ => rfl) y₄.1 y₃.1 hover
    have h2 := GlobalTheory.FlagTan.evR_frMap (hβ k).1 hmap₂
    letI : Algebra T.Q.c.F T0.Fr := io.toAlgebra
    have h3 := GlobalTheory.FlagTan.evR_frMap (hβ k).1 hmap
    rw [hy₂] at h2
    show evR _ _ (g k) y₄.1 = _
    rw [h1, h2, h3]
    exact congrArg iT (DFunLike.congr_fun hφ _)
  have hsum : evI y₄ (∑ k, y k • g k) = iT (∑ k, τ (y k) * i (evI pt (β k))) := by
    show evR _ _ (∑ k, y k • g k) y₄.1 = _

    rw [GlobalTheory.SupDescent.evR_sum, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul]
    exact congrArg₂ (· * ·) rfl (hval k)
  have ho₂ : OverLa la T''.V (iT.comp τ) (e₃ * e'') := ho.bc iT he₃ hv₃
  have h : 0 ≤ nval T''.V (e₃ * e'') (evI y₄ (∑ k, y k • g k)) := hint _ ⟨PtV.mk (cls := algCls C.d.Xo₂ C.d.c₂) (PY := Unit) (lies := fun _ _ _ _ => True) la ho₂ y₄ hT''
    () trivial, rfl⟩
  rw [hsum, nval_bc iT he₃ hv₃] at h
  exact valV_le_one_of_nval ho.1 h

end GlobalTheory.CoverLiftVal
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BaseSectionsValuesIntegralAtCoverLiftStatement

section

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.NX Formalism.IndefR.FWT Formalism.IndefR.Lev GlobalTheory.CoverRead GlobalTheory.TowerCov GlobalTheory.Member
open scoped TensorProduct Matrix
open Classical

theorem _root_.GlobalTheory.T.baseSections_values_integral_at_coverLift : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, ∀ C : Cover T j σ, C.IsUnif → ∀ (la : HeightOneSpectrum (𝓞 C.d.c₂.F)) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (m : ℕ) (β : Fin m → Rul (T.Q.Xo j) T.Q.c) (g : Fin m → Rul C.d.Xo₂ C.d.c₂), (∀ k, β k ∈ sec (T.Q.Xo j) T.Q.c a n) → (∀ k, g k ∈ sec C.d.Xo₂ C.d.c₂ a n) → (∀ k, C.IsPull (β k) (g k)) → ∀ y : Fin m → C.d.c₂.F, (∀ v ∈ valSet C.d.Xo₂ C.d.c₂ (algCls C.d.Xo₂ C.d.c₂) la, 0 ≤ v (∑ k, y k • g k)) → ∀ (T0 : CDVR) (io : T.Q.c.F →+* T0.Fr) (pt : IntFr (T.Q.Xo j) T.Q.c T0 io), T0.FinRes → ∀ (T' : CDVR) (i : T0.Fr →+* T'.Fr) (e' : ℕ) (τ : C.d.c₂.F →+* T'.Fr) (e'' : ℕ), 0 < e' → (∀ z : T0.Fr, z ≠ 0 → vV T'.V (i z) = (e' : ℤ) * vV T0.V z) → T'.FinRes → (∀ z : T.Q.c.F, τ (C.inc z) = i (io z)) → OverLa la T'.V τ e'' → valV T'.V (∑ k, τ (y k) * i (evI pt (β k))) ≤ 1 := by
  first | exact @GlobalTheory.CoverLiftVal.le_one_at_lift | exact GlobalTheory.CoverLiftVal.le_one_at_lift | (intros; apply GlobalTheory.CoverLiftVal.le_one_at_lift <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralCoverFormPullbackCombination

section

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.NX Formalism.IndefR.FWT Formalism.IndefR.Lev GlobalTheory.CoverRead GlobalTheory.TowerCov GlobalTheory.Member
open scoped TensorProduct Matrix
open Classical

namespace GlobalTheory.CoverPullComb


set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem exists_pull_comb_integral : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → ∀ C : Cover T j σ, C.IsUnif → C.IsPinned a n → ∀ (la : HeightOneSpectrum (𝓞 C.d.c₂.F)) (m : ℕ) (β : Fin m → Rul (T.Q.Xo j) T.Q.c), (∀ k, β k ∈ sec (T.Q.Xo j) T.Q.c a n) → ∀ y : Fin m → C.d.c₂.F, (∑ k, C.σ₂ (y k) • T.phiJ j σ a (β k)) ∈ C.intForms a n {la} → ∃ g : Fin m → Rul C.d.Xo₂ C.d.c₂, (∀ k, g k ∈ sec C.d.Xo₂ C.d.c₂ a n) ∧ (∀ k, C.IsPull (β k) (g k)) ∧ ∀ v ∈ valSet C.d.Xo₂ C.d.c₂ (algCls C.d.Xo₂ C.d.c₂) la, 0 ≤ v (∑ k, y k • g k) := by
  intro D T hL j hj σ hσ a n hD C hU hP la m β hβ y hy
  have hpull : ∀ k, ∃ g₂ ∈ sec C.d.Xo₂ C.d.c₂ a n, C.IsPull (β k) g₂ :=
    fun k => GlobalTheory.CovPull.exists_pull D T hL j hj σ hσ C hU.1 a n (β k) (hβ k)
  choose g hg hgp using hpull
  refine ⟨g, hg, hgp, ?_⟩
  obtain ⟨f₂, ⟨hf₂c, hf₂i⟩, hf₂r⟩ := hy

  let R : Rul C.d.Xo₂ C.d.c₂ →ₛₗ[C.σ₂] (GA D (T.V j σ) → ℂ) :=
    (lieFac (T.Q.Dw j) (xiR D) a : ℂ) •
      ((adel (T.V j σ) C.dict₂ (muPin (T.V j σ) C.dict₂ (T.mu j σ) C.cc₂)).comp (rdU C.U₂))
  have hR : ∀ f, C.rd a f = R f := fun _ => rfl
  have hsum : C.rd a (∑ k, y k • g k) = ∑ k, C.σ₂ (y k) • T.phiJ j σ a (β k) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hR, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smulₛₗ, ← hR, hP.2 (β k) (hβ k) (g k) (hg k) (hgp k)]
  set s := ∑ k, y k • g k with hs
  have hsmem : s ∈ sec C.d.Xo₂ C.d.c₂ a n := Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hg k)
  have hdmem : f₂ - s ∈ sec C.d.Xo₂ C.d.c₂ a n := Submodule.sub_mem _ hf₂c.1 hsmem
  have hd0 : C.rd a (f₂ - s) = 0 := by
    rw [hR, map_sub, ← hR, ← hR, hf₂r, hsum, sub_self]
  have heq : f₂ = s := by
    by_contra hne
    have hne' : f₂ - s ≠ 0 := sub_ne_zero.mpr hne
    have hli : LinearIndependent C.d.c₂.F (fun _ : Fin 1 => f₂ - s) := by
      rw [Fintype.linearIndependent_iff]
      intro c hc i
      rw [Fin.sum_univ_one] at hc
      have hi : i = 0 := Subsingleton.elim _ _
      subst hi
      by_contra hc0
      apply hne'
      calc f₂ - s = (c 0)⁻¹ • (c 0 • (f₂ - s)) := by rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
        _ = 0 := by rw [hc, smul_zero]
    have hC := GlobalTheory.CoverIndep.cover_rd_linearIndependent D T hL j hj σ hσ C hU hP.1 a n hD 1 (fun _ => f₂ - s)
      (fun _ => hdmem) hli
    exact hC.ne_zero 0 hd0
  intro v hv
  rw [← heq]
  exact hf₂i la rfl v hv

end GlobalTheory.CoverPullComb
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralCoverFormPullbackCombinationStatement

section

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.NX Formalism.IndefR.FWT Formalism.IndefR.Lev GlobalTheory.CoverRead GlobalTheory.TowerCov GlobalTheory.Member
open scoped TensorProduct Matrix
open Classical

theorem _root_.GlobalTheory.T.exists_integral_cover_form_pullback_combination : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → ∀ C : Cover T j σ, C.IsUnif → C.IsPinned a n → ∀ (la : HeightOneSpectrum (𝓞 C.d.c₂.F)) (m : ℕ) (β : Fin m → Rul (T.Q.Xo j) T.Q.c), (∀ k, β k ∈ sec (T.Q.Xo j) T.Q.c a n) → ∀ y : Fin m → C.d.c₂.F, (∑ k, C.σ₂ (y k) • T.phiJ j σ a (β k)) ∈ C.intForms a n {la} → ∃ g : Fin m → Rul C.d.Xo₂ C.d.c₂, (∀ k, g k ∈ sec C.d.Xo₂ C.d.c₂ a n) ∧ (∀ k, C.IsPull (β k) (g k)) ∧ ∀ v ∈ valSet C.d.Xo₂ C.d.c₂ (algCls C.d.Xo₂ C.d.c₂) la, 0 ≤ v (∑ k, y k • g k) := by
  first | exact @GlobalTheory.CoverPullComb.exists_pull_comb_integral | exact GlobalTheory.CoverPullComb.exists_pull_comb_integral | (intros; apply GlobalTheory.CoverPullComb.exists_pull_comb_integral <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TraceCombinationCoverFormIntegralOverPrime

section

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.NX Formalism.IndefR.FWT Formalism.IndefR.Lev GlobalTheory.CoverRead GlobalTheory.TowerCov GlobalTheory.Member
open scoped TensorProduct Matrix
open Classical

noncomputable section

namespace GlobalTheory.TraceIdem

theorem nval_nonneg_iff {T : CDVR} {e : ℕ} (he : 0 < e) (z : T.Fr) : 0 ≤ nval T.V e z ↔ valV T.V z ≤ 1 := by
  by_cases hz : z = 0
  · subst hz; simp [nval]
  rw [nval_of_ne hz, EReal.coe_nonneg]
  have he' : (0 : ℝ) < e := by exact_mod_cast he
  rw [div_nonneg_iff]
  have h1 : valV T.V z ≠ 0 := valV_ne_zero hz
  constructor
  · rintro (⟨h, -⟩ | ⟨-, h⟩)
    · have h' : 0 ≤ vV T.V z := by exact_mod_cast h
      unfold vV at h'
      rw [← WithZero.log_le_log h1 one_ne_zero, WithZero.log_one]; omega
    · linarith
  · intro h
    left
    refine ⟨?_, he'.le⟩
    have := (WithZero.log_le_log h1 one_ne_zero).2 h
    rw [WithZero.log_one] at this
    have h' : 0 ≤ vV T.V z := by unfold vV; omega
    exact_mod_cast h'

theorem trace_comb_integral : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → holSub0 (T.U j σ).X (laU (T.U j σ) a n) ≤ Submodule.span ℂ (rdU (T.U j σ) '' {f | f ∈ sec (T.Q.Xo j) T.Q.c a n ∧ rdU (T.U j σ) f ∈ holSub0 (T.U j σ).X (laU (T.U j σ) a n)}) → (∀ k ∈ T.Kf j σ, ∀ h, T.mu j σ (h * k) = T.mu j σ h) → ∀ C : Cover T j σ, C.IsUnif → C.IsPinned a n → ∀ (la : HeightOneSpectrum (𝓞 C.d.c₂.F)) (p : HeightOneSpectrum (𝓞 T.Q.c.F)), (letI : Algebra T.Q.c.F C.d.c₂.F := C.inc.toAlgebra; la.asIdeal.under (𝓞 T.Q.c.F) = p.asIdeal) → ∀ (m : ℕ) (β : Fin m → Rul (T.Q.Xo j) T.Q.c), (∀ k, β k ∈ sec (T.Q.Xo j) T.Q.c a n ∧ rdU (T.U j σ) (β k) ∈ holSub0 (T.U j σ).X (laU (T.U j σ) a n)) → (∀ k, ∀ v ∈ valSet (T.Q.Xo j) T.Q.c (algCls (T.Q.Xo j) T.Q.c) p, 0 ≤ v (β k)) → ∀ y : Fin m → C.d.c₂.F, (∑ k, C.σ₂ (y k) • T.phiJ j σ a (β k)) ∈ C.intForms a n {la} → ∃ N : ℕ, ∀ b : 𝓞 C.d.c₂.F, (∀ la' : HeightOneSpectrum (𝓞 C.d.c₂.F), la' ≠ la → (letI : Algebra T.Q.c.F C.d.c₂.F := C.inc.toAlgebra; la'.asIdeal.under (𝓞 T.Q.c.F) = p.asIdeal) → b ∈ la'.asIdeal ^ N) → ∀ v ∈ valSet (T.Q.Xo j) T.Q.c (algCls (T.Q.Xo j) T.Q.c) p, 0 ≤ v (∑ k, (letI : Algebra T.Q.c.F C.d.c₂.F := C.inc.toAlgebra; Algebra.trace T.Q.c.F C.d.c₂.F ((b : C.d.c₂.F) * y k)) • β k) := by
  intro D T hL j hj σ hσ a n hD hspan hmu C hU hP la p hla m β hβ hβi y hφ
  obtain ⟨g, hgs, hgp, hgi⟩ := (GlobalTheory.T.exists_integral_cover_form_pullback_combination D T hL j hj σ hσ a n hD C hU hP la m β (fun k => (hβ k).1) y hφ)
  letI : Algebra T.Q.c.F C.d.c₂.F := C.inc.toAlgebra
  obtain ⟨N, hN⟩ := GlobalTheory.T.trace_integral_of_small_at_other_places T.Q.c.F C.d.c₂.F p la hla m y
  refine ⟨N, fun b hb v hv => ?_⟩
  have hx : ∀ k, 0 ≤ v (β k) := fun k => hβi k v hv
  obtain ⟨⟨q, T0, io, e, ho, pt, hpt, eta, heta, rfl⟩, rfl⟩ := hv
  have hx' : ∀ k, valV T0.V (evI pt (β k)) ≤ 1 := fun k => (nval_nonneg_iff ho.1 _).1 (hx k)
  have hs : ∀ (s : Finset (Fin m)) (t : Fin m → T.Q.c.F),
      evI pt (∑ k ∈ s, t k • β k) = ∑ k ∈ s, io (t k) * evI pt (β k) := by
    intro s t
    induction s using Finset.induction_on with
    | empty => simpa using (isEval_evI pt).zero ()
    | insert k s hk ih => rw [Finset.sum_insert hk, Finset.sum_insert hk, evI_add, evI_smul, ih]
  show 0 ≤ nval T0.V e (evI pt _)
  rw [nval_nonneg_iff ho.1, hs]
  exact hN b hb T0 hpt io e ho (fun k => evI pt (β k)) hx'
    (fun T' i e' τ e'' he' hi hT' hτ ho' =>
      GlobalTheory.T.baseSections_values_integral_at_coverLift D T hL j hj σ C hU la a n m β g (fun k => (hβ k).1) hgs hgp y hgi T0 io pt hpt T' i e' τ e'' he' hi hT' hτ ho')

end GlobalTheory.TraceIdem
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TraceCombinationCoverFormIntegralOverPrimeStatement

section

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.NX Formalism.IndefR.FWT Formalism.IndefR.Lev GlobalTheory.CoverRead GlobalTheory.TowerCov GlobalTheory.Member
open scoped TensorProduct Matrix
open Classical

theorem _root_.GlobalTheory.T.traceCombination_coverForm_integral_over_prime : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → holSub0 (T.U j σ).X (laU (T.U j σ) a n) ≤ Submodule.span ℂ (rdU (T.U j σ) '' {f | f ∈ sec (T.Q.Xo j) T.Q.c a n ∧ rdU (T.U j σ) f ∈ holSub0 (T.U j σ).X (laU (T.U j σ) a n)}) → (∀ k ∈ T.Kf j σ, ∀ h, T.mu j σ (h * k) = T.mu j σ h) → ∀ C : Cover T j σ, C.IsUnif → C.IsPinned a n → ∀ (la : HeightOneSpectrum (𝓞 C.d.c₂.F)) (p : HeightOneSpectrum (𝓞 T.Q.c.F)), (letI : Algebra T.Q.c.F C.d.c₂.F := C.inc.toAlgebra; la.asIdeal.under (𝓞 T.Q.c.F) = p.asIdeal) → ∀ (m : ℕ) (β : Fin m → Rul (T.Q.Xo j) T.Q.c), (∀ k, β k ∈ sec (T.Q.Xo j) T.Q.c a n ∧ rdU (T.U j σ) (β k) ∈ holSub0 (T.U j σ).X (laU (T.U j σ) a n)) → (∀ k, ∀ v ∈ valSet (T.Q.Xo j) T.Q.c (algCls (T.Q.Xo j) T.Q.c) p, 0 ≤ v (β k)) → ∀ y : Fin m → C.d.c₂.F, (∑ k, C.σ₂ (y k) • T.phiJ j σ a (β k)) ∈ C.intForms a n {la} → ∃ N : ℕ, ∀ b : 𝓞 C.d.c₂.F, (∀ la' : HeightOneSpectrum (𝓞 C.d.c₂.F), la' ≠ la → (letI : Algebra T.Q.c.F C.d.c₂.F := C.inc.toAlgebra; la'.asIdeal.under (𝓞 T.Q.c.F) = p.asIdeal) → b ∈ la'.asIdeal ^ N) → ∀ v ∈ valSet (T.Q.Xo j) T.Q.c (algCls (T.Q.Xo j) T.Q.c) p, 0 ≤ v (∑ k, (letI : Algebra T.Q.c.F C.d.c₂.F := C.inc.toAlgebra; Algebra.trace T.Q.c.F C.d.c₂.F ((b : C.d.c₂.F) * y k)) • β k) := by
  first | exact @GlobalTheory.TraceIdem.trace_comb_integral | exact GlobalTheory.TraceIdem.trace_comb_integral | (intros; apply GlobalTheory.TraceIdem.trace_comb_integral <;> assumption)
end
end
